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

using namespace llvm;

namespace {
    struct OMPRacePass : public llvm::FunctionPass {
        bool runOnFunction(llvm::Function &F) override {
            if (!F.getName().startswith(".omp_outlined."))
                return false; // not function of interest

            errs() << "Working on OpenMP outlined function " << F.getName() << '\n';

            // form segments
            for (auto &bb: F) {
                for (auto &op: bb) {
                    if (op.isTerminator())
                        break; // next BB
                    else if (op.getOpcode() == Instruction::Call) {
                        auto *callee = op.getOperand(op.getNumOperands() - 1);
                        assert(callee->getType()->isPointerTy() &&
                               "call op's last argument should be a ptr to function");
                        errs() << "callee name: " << callee->getName() << '\n';
                    }
                }
            }

            auto &baa = getAnalysis<BasicAAWrapperPass>().getResult();
            auto &snaaa = getAnalysis<ScopedNoAliasAAWrapperPass>().getResult();
            auto &tbaa = getAnalysis<TypeBasedAAWrapperPass>().getResult();
            auto &gaa = getAnalysis<GlobalsAAWrapperPass>().getResult();
            auto &scevaa = getAnalysis<SCEVAAWrapperPass>().getResult();
            auto &cflaaa = getAnalysis<CFLAndersAAWrapperPass>().getResult();
            auto &cflsaa = getAnalysis<CFLSteensAAWrapperPass>().getResult();

            return false;
        }

        static char ID;

        OMPRacePass() : FunctionPass(ID) {}

        void getAnalysisUsage(AnalysisUsage &usage) const override {
            usage.setPreservesAll();

            usage.addRequired<BasicAAWrapperPass>();
            // usage.addRequired<TargetLibraryInfoWrapperPass>();

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
