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

namespace {
    struct Segment {
        BasicBlock *parent = nullptr;
        vector<Instruction *> instructions;
        vector<Segment *> pred, succ;
    };

    // we need this to compute lock set
    unordered_map<BasicBlock *, vector<Segment *>> mapBB2Seg;

    struct OMPRacePass : public llvm::FunctionPass {
        bool runOnFunction(llvm::Function &F) override {
            if (!F.getName().startswith(".omp_outlined."))
                return false; // not function of interest

            AAQueryInfo aaqi;
            auto &baa = getAnalysis<BasicAAWrapperPass>().getResult();
            auto &snaaa = getAnalysis<ScopedNoAliasAAWrapperPass>().getResult();
            auto &tbaa = getAnalysis<TypeBasedAAWrapperPass>().getResult();
            auto &gaa = getAnalysis<GlobalsAAWrapperPass>().getResult();
            auto &scevaa = getAnalysis<SCEVAAWrapperPass>().getResult();
            auto &cflaaa = getAnalysis<CFLAndersAAWrapperPass>().getResult();
            auto &cflsaa = getAnalysis<CFLSteensAAWrapperPass>().getResult();

            errs() << "Working on OpenMP outlined function " << F.getName() << '\n';

            // form segments
            for (auto &bb: F) {
                Segment *curSeg = nullptr;
                for (auto &op: bb) {
                    if (curSeg == nullptr) {
                        curSeg = new Segment();
                        curSeg->parent = &bb;
                        // we compute the predecessors after we are done with all BBs
                        mapBB2Seg[&bb].push_back(curSeg);
                    }
                    curSeg->instructions.push_back(&op);
                    if (op.isTerminator()) {
                        // BB terminating. Finish current segment.
                        // we compute the successors after we are done with all BBs
                        mapBB2Seg[&bb].push_back(curSeg);
                        break;
                    }

                    if (auto *callInst = dyn_cast<CallInst>(&op)) {
                        Function *callee = callInst->getCalledFunction();
                        if (callee->getName().equals("omp_set_lock") ||
                            callee->getName().equals("omp_unset_lock") ||
                            callee->getName().equals("__kmpc_critical") ||
                            callee->getName().equals("__kmpc_end_critical")) {
                            // syncing operations, start new segment and chain it with prev segment
                            auto *newSeg = new Segment();
                            newSeg->parent = &bb;
                            newSeg->pred.push_back(curSeg);
                            curSeg->succ.push_back(newSeg);
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
                for (auto *pred: predecessors(&bb))
                    first->pred.push_back(mapBB2Seg[pred].back());

                // ending segment so successors are first segments of BB's successor BBs.
                Segment *last = mapBB2Seg[&bb].back();
                for (auto *succ: successors(&bb))
                    first->pred.push_back(mapBB2Seg[succ].front());
            }

            // compute the lock set
            // first, we make a list of all the locks
            vector<MemoryLocation> explicitLocks; // for omp_lock_t
            unordered_set<Value *> critLocks; // for critical sections
            for (auto &bb: F) {
                for (auto &op: bb)
                    if (auto *callInst = dyn_cast<CallInst>(&op)) {
                        Function *callee = callInst->getCalledFunction();
                        if (callee->getName().equals("omp_set_lock") ||
                            callee->getName().equals("omp_unset_lock")) {
                            Value *regLock = callInst->getArgOperand(0);
                            auto *loadLockInst = dyn_cast<LoadInst>(regLock);
                            MemoryLocation memLoc = MemoryLocation::get(loadLockInst);
                            // if this is a new lock
                            auto it = find_if(explicitLocks.begin(), explicitLocks.end(),
                                              [&](const MemoryLocation &o) {
                                                  AliasResult aliasResult
                                                          = getAliasResult(memLoc, o, aaqi,
                                                                           baa, snaaa, tbaa, gaa,
                                                                           scevaa, cflaaa, cflsaa);
                                                  return aliasResult == MustAlias ||
                                                         aliasResult == PartialAlias;
                                              });
                            if (it == explicitLocks.end())
                                explicitLocks.push_back(memLoc);
                        } else if (callee->getName().equals("__kmpc_critical") ||
                                   callee->getName().equals("__kmpc_end_critical")) {
                            Value *lock = callInst->getArgOperand(2);
                            if (critLocks.find(lock) == critLocks.end())
                                critLocks.insert(lock);
                        }
                    }
            }
            errs() << "Number of omp_lock_t locks detected: " << explicitLocks.size() << '\n';
            errs() << "Number of different critical sections detected: " << critLocks.size() << '\n';
            // TODO

            // compute happen-before relation
            // TODO


            // TODO: access with atomicrmw should ignore lock set. They are generated with #pragma omp atomic

            errs() << '\n';
            return false;
        }

        AliasResult getAliasResult(
                const MemoryLocation &A, const MemoryLocation &B,
                AAQueryInfo &AAQI,
                BasicAAResult &baa,
                ScopedNoAliasAAResult &snaaa,
                TypeBasedAAResult &tbaa,
                GlobalsAAResult &gaa,
                SCEVAAResult &scevaa,
                CFLAndersAAResult &cflaaa,
                CFLSteensAAResult &cflsaa
        ) {
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
