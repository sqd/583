#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/ScopedNoAliasAA.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"
#include "llvm/Analysis/CFLAndersAliasAnalysis.h"
#include "llvm/Analysis/CFLSteensAliasAnalysis.h"
#include "llvm/IR/Instruction.def"
#include "llvm/Support/Format.h"
#include "llvm/IR/CFG.h"

#include <vector>
#include <unordered_map>
#include <unordered_set>

using namespace llvm;
using namespace std;

struct Lock {
    enum LockType {
        ExplicitLock,
        CriticalSectionLock
    } const type;
    union {
        MemoryLocation explicitLock;
        Value *criticalSectionLock;
    } const value;

    explicit Lock(const MemoryLocation &mem) : type(ExplicitLock), value({.explicitLock = mem}) {}

    explicit Lock(Value *crit) : type(CriticalSectionLock), value({.criticalSectionLock = crit}) {}

    bool operator==(const Lock &other) const {
        if (type != other.type)
            return false;
        switch (type) {
            case Lock::ExplicitLock:
                return value.explicitLock == other.value.explicitLock;
            case Lock::CriticalSectionLock:
                return value.criticalSectionLock == other.value.criticalSectionLock;
            default:
                assert(false && "Type not considered");
                return false; // to appease the totality god
        }
    }
};

namespace std {
    template<>
    struct hash<Lock> {
        std::size_t operator()(Lock const &lock) const noexcept {
            switch (lock.type) {
                case Lock::ExplicitLock:
                    return (size_t) lock.value.explicitLock.Ptr;
                case Lock::CriticalSectionLock:
                    return reinterpret_cast<size_t>(lock.value.criticalSectionLock);
                default:
                    return 0;
            }
        }
    };
}

struct Segment {
    BasicBlock *parent = nullptr;
    vector<Instruction *> instructions;
    vector<Segment *> pred, succ;
    unordered_set<Lock> lockSet;

    unordered_set<Lock> outSet;

    void dump() {
        parent->printAsOperand(errs(), false);
        errs() << '\n';
        for (Instruction *op: instructions)
            errs() << *op << '\n';
    }
};

template<typename T>
void unionWith(unordered_set<T> &target, const unordered_set<T> &with) {
    for (const T &t: with)
        target.insert(t);
}

namespace {
    struct AASummary {
        AAQueryInfo AAQI;
        BasicAAResult baa;
        ScopedNoAliasAAResult snaaa;
        TypeBasedAAResult tbaa;
        GlobalsAAResult gaa;
        SCEVAAResult scevaa;
        CFLAndersAAResult cflaaa;
        CFLSteensAAResult cflsaa;

        AliasResult alias(const MemoryLocation &A, const MemoryLocation &B) {
            AAQueryInfo::LocPair Locs(A, B);

            // Return cached alias result if it exists
            auto hit = AAQI.AliasCache.find(Locs);
            if (hit != AAQI.AliasCache.end()) {
                return hit->second;
            }
            // Go through all passes and cache strictest alias result
            vector<AliasResult> results;
            auto I = AAQueryInfo();
            results.push_back(baa.alias(A, B, I));
            I = AAQueryInfo();
            results.push_back(snaaa.alias(A, B, I));
            I = AAQueryInfo();
            results.push_back(tbaa.alias(A, B, I));
            I = AAQueryInfo();
            results.push_back(gaa.alias(A, B, I));
            I = AAQueryInfo();
            results.push_back(scevaa.alias(A, B, I));
            I = AAQueryInfo();
            results.push_back(cflaaa.alias(A, B, I));
            I = AAQueryInfo();
            results.push_back(cflsaa.alias(A, B, I));

            for (auto &R : results) {
                if (R == MustAlias) {
                    AAQI.AliasCache.insert(make_pair(Locs, R));
                    return R;
                }
            }
            for (auto &R : results) {
                if (R == PartialAlias) {
                    AAQI.AliasCache.insert(make_pair(Locs, R));
                    return R;
                }
            }
            for (auto &R : results) {
                if (R == NoAlias) {
                    AAQI.AliasCache.insert(make_pair(Locs, R));
                    return R;
                }
            }
            return MayAlias;
        }
    };

    template<typename C>
    typename C::iterator findLockIn(const Lock &target, C &lockSet, AASummary &aas) {
        switch (target.type) {
            case Lock::ExplicitLock:
                return find_if(lockSet.begin(), lockSet.end(),
                               [&](const Lock &lock) {
                                   if (lock.type != target.type)
                                       return false;
                                   AliasResult aliasResult
                                           = aas.alias(target.value.explicitLock, lock.value.explicitLock);
                                   return aliasResult == MustAlias ||
                                          aliasResult == PartialAlias;
                               });
            case Lock::CriticalSectionLock:
                return find_if(lockSet.begin(), lockSet.end(),
                               [&](const Lock &lock) {
                                   if (lock.type != target.type)
                                       return false;
                                   return lock.value.criticalSectionLock == target.value.criticalSectionLock;
                               });
            default:
                assert(false);
        }
    }

    bool updateLockSet(Segment *seg, unordered_set<Lock> allLocks, AASummary &aas) {
        seg->lockSet.clear();
        for (Segment *pred: seg->pred)
            unionWith(seg->lockSet, pred->outSet);
        unordered_set<Lock> oldOutSeg = std::move(seg->outSet);
        seg->outSet = seg->lockSet;

        Instruction *endOp = seg->instructions.back();
        if (endOp->isTerminator()) {
            // this segment ends naturally, nothing is killed/generated
            return false;
        } else {
            // this segment ends because of a syncing operation
            // which is a function call
            auto *callInst = dyn_cast<CallInst>(endOp);
            Function *callee = callInst->getCalledFunction();
            if (callee->getName().equals("omp_set_lock")) {
                // gen a new lock
                MemoryLocation memLoc = MemoryLocation::get(dyn_cast<LoadInst>(callInst->getArgOperand(0)));
                Lock newLock = *findLockIn(Lock(memLoc), allLocks, aas);
                seg->outSet.insert(newLock);
                return seg->outSet != oldOutSeg;
            } else if (callee->getName().equals("omp_unset_lock")) {
                // kill a lock
                MemoryLocation memLoc = MemoryLocation::get(dyn_cast<LoadInst>(callInst->getArgOperand(0)));
                Lock deadLock = *findLockIn(Lock(memLoc), allLocks, aas);
                seg->outSet.erase(deadLock);
                return seg->outSet != oldOutSeg;
            } else if (callee->getName().equals("__kmpc_critical")) {
                // gen a new lock
                Value *critLock = callInst->getArgOperand(2);
                Lock newLock = *findLockIn(Lock(critLock), allLocks, aas);
                seg->outSet.insert(newLock);
                return seg->outSet != oldOutSeg;
            } else if (callee->getName().equals("__kmpc_end_critical")) {
                // kill a lock
                Value *critLock = callInst->getArgOperand(2);
                Lock deadLock = *findLockIn(Lock(critLock), allLocks, aas);
                seg->outSet.erase(deadLock);
                return seg->outSet != oldOutSeg;
            } else {
                assert(false);
            }
        }
    }

    struct OMPRacePass : public llvm::FunctionPass {
        bool runOnFunction(llvm::Function &F) override {
            if (!F.getName().startswith(".omp_outlined."))
                return false; // not function of interest

            AASummary aas = {
                    AAQueryInfo(),
                    getAnalysis<BasicAAWrapperPass>().getResult(),
                    getAnalysis<ScopedNoAliasAAWrapperPass>().getResult(),
                    getAnalysis<TypeBasedAAWrapperPass>().getResult(),
                    std::move(getAnalysis<GlobalsAAWrapperPass>().getResult()),
                    std::move(getAnalysis<SCEVAAWrapperPass>().getResult()),
                    std::move(getAnalysis<CFLAndersAAWrapperPass>().getResult()),
                    std::move(getAnalysis<CFLSteensAAWrapperPass>().getResult())
            };
            errs() << "Working on OpenMP outlined function " << F.getName() << '\n';

            unordered_map<BasicBlock *, vector<Segment *>> mapBB2Seg;

            // form segments
            unordered_set<Segment *> allSegs;
            for (auto &bb: F) {
                Segment *curSeg = nullptr;
                for (auto &op: bb) {
                    if (curSeg == nullptr) {
                        curSeg = new Segment();
                        allSegs.insert(curSeg);
                        curSeg->parent = &bb;
                        // we compute the predecessors after we are done with all BBs
                        mapBB2Seg[&bb].push_back(curSeg);
                    }
                    curSeg->instructions.push_back(&op);
                    if (op.isTerminator()) {
                        // BB terminating. Stop processing current segment.
                        // we compute the successors after we are done with all BBs
                        break;
                    }

                    if (auto *callInst = dyn_cast<CallInst>(&op)) {
                        Function *callee = callInst->getCalledFunction();
                        if (callee->getName().equals("omp_set_lock") ||
                            callee->getName().equals("omp_unset_lock") ||
                            callee->getName().equals("__kmpc_critical") ||
                            callee->getName().equals("__kmpc_end_critical")) {

                            // syncing operations, start a new segment
                            auto *newSeg = new Segment();
                            allSegs.insert(newSeg);
                            newSeg->parent = &bb;
                            curSeg = newSeg;
                            mapBB2Seg[&bb].push_back(curSeg);
                        }
                    }
                }
            }

            // fill segments' predecessor/successor info
            for (auto &bb: F) {
                // first segment so predecessors are ending segments of BB's predecessor BBs.
                Segment *first = mapBB2Seg[&bb].front();
                for (auto *predBB: predecessors(&bb))
                    first->pred.push_back(mapBB2Seg[predBB].back());

                // ending segment so successors are first segments of BB's successor BBs.
                Segment *last = mapBB2Seg[&bb].back();
                for (auto *succBB: successors(&bb))
                    last->succ.push_back(mapBB2Seg[succBB].front());

                // pred/succ inside BB
                vector<Segment *> &segOfBB = mapBB2Seg[&bb];
                for (auto it = segOfBB.begin(); it != segOfBB.end() && it + 1 != segOfBB.end(); it++) {
                    auto next = it + 1;
                    (*it)->succ.push_back(*next);
                    (*next)->pred.push_back(*it);
                }
            }

#ifdef VERBOSE_DEBUG
            for (BasicBlock &bb: F) {
                bb.printAsOperand(errs(), false);
                errs() << '\n';
                for (Segment *seg: mapBB2Seg[&bb]) {
                    seg->dump();
                    errs() << "pred: " << seg->pred.size() << ' ';
                    for (Segment *pred: seg->pred) {
                        pred->parent->printAsOperand(errs(), false);
                        errs() << ' ';
                    }
                    errs() << '\n';
                    errs() << "succ: " << seg->succ.size() << ' ';
                    for (Segment *succ: seg->succ) {
                        succ->parent->printAsOperand(errs(), false);
                        errs() << ' ';
                    }
                    errs() << '\n';
                    errs() << "            -----------------------------------------------------------------\n";
                }
                errs() << "=============================================================================\n";
            }
#endif

            // compute the lock set
            // first, we make a list of all the locks
            unordered_set<Lock> allLocks;
            for (auto &bb: F) {
                for (auto &op: bb)
                    if (auto *callInst = dyn_cast<CallInst>(&op)) {
                        Function *callee = callInst->getCalledFunction();
                        if (callee->getName().equals("omp_set_lock") ||
                            callee->getName().equals("omp_unset_lock")) {

                            MemoryLocation memLoc = MemoryLocation::get(dyn_cast<LoadInst>(callInst->getArgOperand(0)));
                            // is this a new lock?
                            if (findLockIn(Lock(memLoc), allLocks, aas) == allLocks.end())
                                allLocks.emplace(memLoc);
                        } else if (callee->getName().equals("__kmpc_critical") ||
                                   callee->getName().equals("__kmpc_end_critical")) {

                            Value *critLock = callInst->getArgOperand(2);
                            // is this a new lock?
                            if (findLockIn(Lock(critLock), allLocks, aas) == allLocks.end())
                                allLocks.emplace(critLock);
                        }
                    }
            }
            errs() << "Number of locks detected: " << allLocks.size() << '\n';


            // now we have all the locks, we actually compute the lock set with a general DFA
#ifdef VERBOSE_DEBUG
            for (int i = 0; i < 5; i++) {
                bool updated = false;
                errs() << "\n\niter " << i << "\n";
                for (Segment *seg: allSegs)
                    if (updateLockSet(seg, allLocks, aas)) {
                        errs() << ".........\n";
                        seg->dump();
                        errs() << "\n.........\n";
                        updated = true;
                    }
                for (Segment *seg: allSegs) {
                    seg->dump();
                    if (!seg->lockSet.empty())
                        errs() << "!!!!!!!" << seg->lockSet.size() << "\n";
                    if (!seg->outSet.empty())
                        errs() << "???????" << seg->outSet.size() << "\n";
                    errs() << '\n';
                }
                if (!updated)
                    break;
            }
#endif
            bool updated = true;
            while (updated) {
                updated = false;
                for (Segment *seg: allSegs)
                    updated = updated || updateLockSet(seg, allLocks, aas);
            }

            // compute happen-before relation
            // TODO


            // TODO: access with atomicrmw should ignore lock set. They are generated with #pragma omp atomic

            errs() << '\n';
            return false;
        }

        static char ID;

        OMPRacePass() : FunctionPass(ID) {}

        void getAnalysisUsage(AnalysisUsage &usage) const override {
            usage.setPreservesAll();

            usage.addRequired<BasicAAWrapperPass>();
            usage.addRequired<ScopedNoAliasAAWrapperPass>();
            usage.addRequired<TypeBasedAAWrapperPass>();
            usage.addRequired<GlobalsAAWrapperPass>();
            usage.addRequired<SCEVAAWrapperPass>();
            usage.addRequired<CFLAndersAAWrapperPass>();
            usage.addRequired<CFLSteensAAWrapperPass>();
        };
    };

    char OMPRacePass::ID = 0;
}


static RegisterPass<OMPRacePass> reg("omprace", "OpenMP race condition detector", true, true);
