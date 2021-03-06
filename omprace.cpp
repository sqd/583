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
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/Analysis/MemoryLocation.h"

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <fstream>

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

MemoryLocation getMemLoc(Value *v) {
    if (auto op = dyn_cast<LoadInst>(v))
        return MemoryLocation::get(op);
    if (auto op = dyn_cast<AllocaInst>(v))
        return MemoryLocation::get(op);
    assert(false);
}

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
        try {
            I = AAQueryInfo();
            results.push_back(cflaaa.alias(A, B, I));
        } catch (std::bad_function_call &) {}
        try {
            I = AAQueryInfo();
            results.push_back(cflsaa.alias(A, B, I));
        } catch (std::bad_function_call &) {}

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

struct Segment {
    BasicBlock *parent = nullptr;
    vector<Instruction *> instructions;
    vector<Segment *> pred, succ;
    unordered_set<Lock> lockSet;
    unordered_set<Segment *> happensBefore;

    unordered_set<Lock> outSet;

    void dump() {
        parent->printAsOperand(errs(), false);
        errs() << '\n';
        for (Instruction *op: instructions)
            errs() << *op << '\n';
    }
};

template<typename T, typename C>
void unionWith(unordered_set<T> &target, const C &with) {
    for (const T &t: with)
        target.insert(t);
}

template<typename T>
bool intersect(const unordered_set<T> &A, const unordered_set<T> &B) {
    return any_of(A.begin(), A.end(), [&](const T &x) {
        return B.find(x) != B.end();
    });
}

int getInstructionIndex(Instruction *target) {
    int index = 0;
    for (Instruction &op: *target->getParent())
        if (&op == target)
            return index;
        else
            ++index;
    return -1;
}

bool printDebugLoc(const DebugLoc &dl) {
    if (auto *dil = dl.get()) {
        string line;
        ifstream source((dil->getDirectory() + "/" + dil->getFilename()).str());
        for (int i = 0; i < dil->getLine(); i++)
            std::getline(source, line);

        errs() << "\x1b[4m" << dil->getFilename() << ":L" << dil->getLine() << "\x1b[0m " << line << '\n';
        return true;
    } else {
        errs() << "no source info :-(\n";
        return false;
    }
}

void printDatarace(Instruction *A, Instruction *B) {
    errs() << "\x1b[1m\x1b[31mpotential data race between:\x1b[0m\n";
    printDebugLoc(A->getDebugLoc());
    A->getParent()->printAsOperand(errs(), false);
    errs() << "(" << getInstructionIndex(A) << "): " << *A << '\n';
    if (B != A) {
        printDebugLoc(B->getDebugLoc());
        B->getParent()->printAsOperand(errs(), false);
        errs() << "(" << getInstructionIndex(B) << "): " << *B << '\n';
    } else
        errs() << "and itself in another thread\n";
}

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

Value *getPointerReference(Instruction *op) {
    if (auto *loadInst = dyn_cast<LoadInst>(op))
        return loadInst->getPointerOperand();
    if (auto *storeInst = dyn_cast<StoreInst>(op))
        return storeInst->getPointerOperand();
    return nullptr;
}

bool detectRace(Instruction *A, Instruction *B, AASummary &aas, unordered_set<Lock> &allLocks,
                const vector<MemoryLocation> &ignoring, const vector<MemoryLocation> &interested) {
    auto codeA = A->getOpcode(), codeB = B->getOpcode();
    if ((codeA == Instruction::Store && codeB == Instruction::Load) ||
        (codeA == Instruction::Load && codeB == Instruction::Store) ||
        (codeA == Instruction::Store && codeB == Instruction::Store)) {

        AliasResult result = aas.alias(MemoryLocation::get(A), MemoryLocation::get(B));
        if ((result == PartialAlias || result == MustAlias) &&
            findLockIn(Lock(MemoryLocation::get(A)), allLocks, aas) == allLocks.end()) {
            // ignore some control blocks for omp; just like locks, they are not meant to be safe in an axiomatic sense
            for (const auto &ignoredMem: ignoring) {
                result = aas.alias(ignoredMem, MemoryLocation::get(A));
                if (result != NoAlias)
                    return false;
            }
            if (find_if(interested.begin(), interested.end(), [&](const MemoryLocation &interestedML) {
                return aas.alias(interestedML, MemoryLocation::get(A)) != NoAlias;
            }) == interested.end()) {
                return false; // not interested
            }
            // found a data race!
            printDatarace(A, B);
            return true;
        }
    }
    return false;
}

namespace {
    bool updateLockSet(Segment *seg, unordered_set<Lock> allLocks, AASummary &aas) {
        seg->lockSet.clear();
        for (Segment *pred: seg->pred)
            unionWith(seg->lockSet, pred->outSet);
        unordered_set<Lock> oldOutSet = std::move(seg->outSet);
        seg->outSet = seg->lockSet;

        Instruction *endOp = seg->instructions.back();
        if (endOp->isTerminator()) {
            // this segment ends naturally, nothing is killed/generated
            return oldOutSet != seg->lockSet;
        } else {
            // this segment ends because of a syncing operation
            // which is a function call
            auto *callInst = dyn_cast<CallInst>(endOp);
            Function *callee = callInst->getCalledFunction();
            if (callee->getName().equals("omp_set_lock") ||
                callee->getName().equals("pthread_mutex_lock")) {
                // gen a new lock
                MemoryLocation memLoc = getMemLoc(callInst->getArgOperand(0));
                Lock newLock = *findLockIn(Lock(memLoc), allLocks, aas);
                seg->outSet.insert(newLock);
                return seg->outSet != oldOutSet;
            } else if (callee->getName().equals("omp_unset_lock") ||
                       callee->getName().equals("pthread_mutex_unlock")) {
                // kill a lock
                MemoryLocation memLoc = getMemLoc(callInst->getArgOperand(0));
                Lock deadLock = *findLockIn(Lock(memLoc), allLocks, aas);
                seg->outSet.erase(deadLock);
                return seg->outSet != oldOutSet;
            } else if (callee->getName().equals("__kmpc_critical")) {
                // gen a new lock
                Value *critLock = callInst->getArgOperand(2);
                Lock newLock = *findLockIn(Lock(critLock), allLocks, aas);
                seg->outSet.insert(newLock);
                return seg->outSet != oldOutSet;
            } else if (callee->getName().equals("__kmpc_end_critical")) {
                // kill a lock
                Value *critLock = callInst->getArgOperand(2);
                Lock deadLock = *findLockIn(Lock(critLock), allLocks, aas);
                seg->outSet.erase(deadLock);
                return seg->outSet != oldOutSet;
            } else if (callee->getName().equals("pthread_cond_wait")) {
                // cv.wait() also kill a lock
                // but cv.signal()/broadcast() does not
                Value *critLock = callInst->getArgOperand(1);
                Lock deadLock = *findLockIn(Lock(critLock), allLocks, aas);
                seg->outSet.erase(deadLock);
                return seg->outSet != oldOutSet;
            }
        }
        return false;
    }

    struct OMPRacePass : public llvm::FunctionPass {
        bool runOnFunction(llvm::Function &F) override {
            if (!F.getName().startswith(".omp_outlined.")) {
                errs() << "Skipping " << F.getName() << "(...): not an OpenMP outlined function.\n";
                return false; // not function of interest
            }

            // test for metadata and output warning if not found
            SmallVector<std::pair<unsigned, MDNode *>, 10> MDs;
            F.getAllMetadata(MDs);
            if (MDs.empty())
                errs() << "\x1b[1m\x1b[31mNo metadata detected. Source info will likely be not available. "
                          "Did you compile with -g -O0?\n\x1b[0m";

            // alias analysis summary
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
            errs() << "\nDetected OpenMP outlined function " << F.getName() << "(...)\n";

            // other records we keep
            auto tli = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
            unordered_map<BasicBlock *, vector<Segment *>> mapBB2Seg;
            vector<MemoryLocation> ompRuntimeControlMem;
            vector<MemoryLocation> interestedSet; // outlined yet shared pointer

            // form segments
            vector<Segment *> allSegs;
            for (auto &bb: F) {
                Segment *curSeg = nullptr;
                for (auto &op: bb) {
                    if (curSeg == nullptr) {
                        curSeg = new Segment();
                        allSegs.push_back(curSeg);
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
                            callee->getName().equals("__kmpc_end_critical") ||
                            callee->getName().equals("pthread_mutex_lock") ||
                            callee->getName().equals("pthread_mutex_unlock") ||
                            callee->getName().equals("pthread_cond_wait") ||
                            callee->getName().equals("pthread_cond_signal") ||
                            callee->getName().equals("__kmpc_barrier")) {

                            // syncing operations, start a new segment
                            auto *newSeg = new Segment();
                            allSegs.push_back(newSeg);
                            newSeg->parent = &bb;
                            curSeg = newSeg;
                            mapBB2Seg[&bb].push_back(curSeg);
                        }
                        if (callee->getName().startswith("__kmpc_for_static_init")) {
                            // we want to filter out omp runtime control memory later
                            for (int i = 3; i <= 6; i++) {
                                Value *arg = callInst->getArgOperand(i);
                                ompRuntimeControlMem.emplace_back(arg);
                            }
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

            // compute the lock set
            // first, we make a canonical list of all the locks and cvs
            // we use the same infrastructure (memory-location-based lock) for CVs
            unordered_set<Lock> allLocks, allCVs;
            for (auto &bb: F) {
                for (auto &op: bb)
                    if (auto *callInst = dyn_cast<CallInst>(&op)) {
                        Function *callee = callInst->getCalledFunction();
                        if (callee->getName().equals("omp_set_lock") ||
                            callee->getName().equals("omp_unset_lock") ||
                            callee->getName().equals("pthread_mutex_lock") ||
                            callee->getName().equals("pthread_mutex_unlock")) {

                            MemoryLocation memLoc = getMemLoc(callInst->getArgOperand(0));
                            // is this a new lock?
                            if (findLockIn(Lock(memLoc), allLocks, aas) == allLocks.end())
                                allLocks.emplace(memLoc);
                        } else if (callee->getName().equals("__kmpc_critical") ||
                                   callee->getName().equals("__kmpc_end_critical")) {

                            Value *critLock = callInst->getArgOperand(2);
                            // is this a new lock?
                            if (findLockIn(Lock(critLock), allLocks, aas) == allLocks.end())
                                allLocks.emplace(critLock);
                        } else if (callee->getName().equals("pthread_cond_wait") ||
                                   callee->getName().equals("pthread_cond_signal") ||
                                   callee->getName().equals("pthread_cond_broadcast")) {
                            if (callee->getName().equals("pthread_cond_wait")) {
                                // this could also introduce a lock not seen before
                                MemoryLocation memLoc = getMemLoc(callInst->getArgOperand(1));
                                // is this a new lock?
                                if (findLockIn(Lock(memLoc), allLocks, aas) == allLocks.end())
                                    allLocks.emplace(memLoc);
                            }
                            // keeping tab of CVs
                            MemoryLocation memLoc = getMemLoc(callInst->getArgOperand(0));
                            // is this a new CV?
                            if (findLockIn(Lock(memLoc), allCVs, aas) == allCVs.end())
                                allCVs.emplace(memLoc);
                        }
                    }
            }

            // compute interested set
            const auto &dl = F.getParent()->getDataLayout();
            for (int i = 2; i < F.arg_size(); i++) {
                Argument *arg = F.getArg(i);
                auto sz = LocationSize::precise(dl.getTypeStoreSize(arg->getType()));
                interestedSet.emplace_back(arg, sz);
            }

            errs() << "Number of locks detected: " << allLocks.size() << "; Number of CVs detected: " << allCVs.size()
                   << '\n';
            errs() << '\n';
            // now we have all the locks canonically, we actually compute the lock set with a general DFA
            bool updated = true;
            while (updated) {
                updated = false;
                for (Segment *seg: allSegs)
                    updated = updated || updateLockSet(seg, allLocks, aas);
#ifdef VERBOSE_DEBUG
                for (auto &BB: F) {
                    for (Segment *seg: mapBB2Seg[&BB]) {
                        seg->dump();
                        if (!seg->lockSet.empty())
                            errs() << "lock set: " << seg->lockSet.size() << "\n";
                        if (!seg->outSet.empty())
                            errs() << "out set: " << seg->outSet.size() << "\n";
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
                    }
                    errs() << '\n';
                    errs() << '\n';
                }
#endif
            }
            // clear outSet since we no longer need it
            for (Segment *seg: allSegs)
                seg->outSet.clear();

            // compute happen-before relations
            for (Segment *seg: allSegs)
                if (auto *callInst = dyn_cast<CallInst>(seg->instructions.back())) {
                    StringRef calledFuncName = callInst->getCalledFunction()->getName();
                    // 1. barrier happen-before
                    if (calledFuncName.equals("__kmpc_barrier")) {
                        // this segment happens before all of its successors
                        unionWith(seg->happensBefore, seg->succ);
                    } // 2. cv happen before
                    else if (calledFuncName.equals("pthread_cond_signal") ||
                             calledFuncName.equals("pthread_cond_broadcast")) {
                        for (Segment *waitSeg: allSegs) {
                            if (auto *waitCallInst = dyn_cast<CallInst>(waitSeg->instructions.back())) {
                                if (waitCallInst->getCalledFunction()->getName().equals("pthread_cond_wait")) {
                                    AliasResult ar = aas.alias(
                                            getMemLoc(callInst->getArgOperand(0)),
                                            getMemLoc(waitCallInst->getArgOperand(0))
                                    );
                                    if (ar == MustAlias ||
                                        ar == PartialAlias) {
                                        // signal/broadcaster happens before the successors of waiter
                                        for (Segment *succ: waitSeg->succ)
                                            succ->happensBefore.insert(seg);
                                    }

                                }
                            }
                        }
                    }

                }
            // happen-before relation is transitive
            updated = true;
            while (updated) {
                updated = false;
                for (Segment *seg: allSegs)
                    for (Segment *after: seg->happensBefore) {
                        for (Segment *afterAfter: after->happensBefore)
                            if (seg->happensBefore.find(afterAfter) == seg->happensBefore.end()) {
                                seg->happensBefore.insert(afterAfter);
                                updated = true;
                            }
                    }
            }

            // detect race!
            bool raceDetected = false;
            for (auto i = allSegs.begin(); i != allSegs.end(); i++)
                for (auto j = i; j != allSegs.end(); j++) {
                    Segment *A = *i, *B = *j;
                    if (A->happensBefore.find(B) == A->happensBefore.end() &&
                        B->happensBefore.find(A) == B->happensBefore.end() &&
                        !intersect(A->lockSet, B->lockSet)) {
                        if (A != B)
                            for (Instruction *opA: A->instructions)
                                for (Instruction *opB: B->instructions) {
                                    raceDetected =
                                            detectRace(opA, opB, aas, allLocks, ompRuntimeControlMem, interestedSet)
                                            || raceDetected;
                                }
                        else {
                            // aesthetic, don't double-loop
                            for (auto k = A->instructions.begin(); k != A->instructions.end(); k++)
                                for (auto l = k; l != A->instructions.end(); l++) {
                                    raceDetected =
                                            detectRace(*k, *l, aas, allLocks, ompRuntimeControlMem, interestedSet)
                                            || raceDetected;
                                }
                        }
                    }
                }

            if (!raceDetected)
                errs() << "no data race detected\n";

            errs() << '\n';
            return false;
        }

        static char ID;

        OMPRacePass() : FunctionPass(ID) {}

        void getAnalysisUsage(AnalysisUsage &usage) const
        override {
            usage.setPreservesAll();

            usage.addRequired<BasicAAWrapperPass>();
            usage.addRequired<ScopedNoAliasAAWrapperPass>();
            usage.addRequired<TypeBasedAAWrapperPass>();
            usage.addRequired<GlobalsAAWrapperPass>();
            usage.addRequired<SCEVAAWrapperPass>();
            usage.addRequired<CFLAndersAAWrapperPass>();
            usage.addRequired<CFLSteensAAWrapperPass>();

            usage.addRequired<TargetLibraryInfoWrapperPass>();
        };
    };

    char OMPRacePass::ID = 0;
}


static RegisterPass<OMPRacePass>

        reg("omprace", "OpenMP race condition detector", true, true);
