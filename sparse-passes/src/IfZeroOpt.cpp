#include "IfZeroOpt.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/Casting.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/Debug.h"
#include "probe_helper.h"
#include <vector>
#include <unordered_map>
#include "BlockCloneHelper.hpp"

using std::vector;
using std::unordered_map;

llvm::PreservedAnalyses IfZeroOpt::run(llvm::Function &F, llvm::FunctionAnalysisManager &AM)
{
    using namespace llvm;
    vector<CallInst *> instrument_checks;
    search_instrumetation_check_calls(F, instrument_checks);
    int id = 0;
    // for a check call in a basic block, split that basic block to two block after the check call.
    for (auto check_call : instrument_checks)
    {
        auto val = check_call->getArgOperand(0);
        auto zero_header = check_call->getParent();
        zero_header->setName("zero_header" + std::to_string(id));
        my_dbg() << "original bb: " << *zero_header << "\n";
        auto not_zero_bb = zero_header->splitBasicBlock(check_call, "not_zero" + std::to_string(id));
        check_call->eraseFromParent();
        my_dbg() << "after split bb: " << *zero_header << "\n";
        my_dbg() << "not_zero bb: " << *not_zero_bb << "\n";
        // if new_bb has multi successors, split it again to make it only have one successor
        if (not_zero_bb->getTerminator()->getNumSuccessors() > 1)
        {
            auto next = not_zero_bb->splitBasicBlock(not_zero_bb->getTerminator());
            my_dbg() << "split not_zero bb: " << *not_zero_bb << "\n";
            my_dbg() << "split not_zero next bb: " << *next << "\n";
        }

        if (not_zero_bb->getSingleSuccessor() && not_zero_bb->getSingleSuccessor()->getSinglePredecessor() == nullptr)
        {
            not_zero_bb->splitBasicBlock(not_zero_bb->getTerminator());
        }
        // value checked if zero
        // create a new basic block the same as not_zero_bb
        auto zero_bb = llvm::BasicBlock::Create(F.getContext(), "zero" + std::to_string(id++), &F);
        // create a map of instruction in not_zero_bb to zero_bb
        unordered_map<Instruction *, Instruction *> instr_map;

        // copy instructions from not_zero_bb to zero_bb
        for (auto &instr : *not_zero_bb)
        {
            auto new_instr = instr.clone();
            instr_map[&instr] = new_instr;
            my_dbg() << "copy: " << instr << " to " << *new_instr << "\n";

            // if val in operands of new_instr, replace it with zero
            for (auto &op : new_instr->operands())
            {
                if (op.get() == val)
                {
                    op.set(ConstantInt::get(val->getType(), 0));
                }
            }

            // replace operand in new_instr with instructions in zero_bb if it is in not_zero_bb
            for (auto &op : new_instr->operands())
            {
                if (auto inst = dyn_cast<Instruction>(op.get()))
                {
                    if (instr_map.find(inst) != instr_map.end())
                    {
                        op.set(instr_map[inst]);
                    }
                }
            }

            new_instr->insertInto(zero_bb, zero_bb->end());
        }
        my_dbg() << "zero bb: " << *zero_bb << "\n";

        zero_header->getTerminator()->eraseFromParent();
        // check whether val equals to zero. if so, branch from bb zero_bb, else not_zero_bb
        auto cmp = CmpInst::Create(
            Instruction::ICmp, CmpInst::ICMP_EQ, val, ConstantInt::get(val->getType(), 0), "", zero_header);
        auto br = BranchInst::Create(zero_bb, not_zero_bb, cmp);
        br->insertInto(zero_header, zero_header->end());
        // replace jump in bb with br
        my_dbg() << "----------------\n";
        my_dbg() << "bb: " << *zero_header << "\n";

        // add phinode in successor of zero_bb and not_zero_bb
        auto succ_num = zero_bb->getTerminator()->getNumSuccessors();
        assert(succ_num <= 1);
        if (succ_num == 1)
        {
            auto succ = zero_bb->getSingleSuccessor();
            assert(succ);
            // for instructions in not_zero_bb that is used in other basic blocks, create a phinode
            for (auto &instr : *not_zero_bb)
            {
                bool need_phi = false;
                for (auto &use : instr.uses())
                {
                    if (auto user_inst = dyn_cast<Instruction>(use.getUser()))
                    {
                        if (user_inst->getParent() != not_zero_bb)
                        {
                            need_phi = true;
                        }
                    }
                }
                if (need_phi)
                {
                    auto phi = PHINode::Create(instr.getType(), 2, "", succ->getFirstNonPHI());
                    phi->addIncoming(&instr, not_zero_bb);
                    phi->addIncoming(instr_map[&instr], zero_bb);
                    instr.replaceUsesWithIf(phi, [not_zero_bb, phi](Use &use) {
                        if (auto inst = dyn_cast<Instruction>(use.getUser()))
                        {
                            return inst != phi && inst->getParent() != not_zero_bb;
                        }
                        return true;
                    });
                }
            }
        }
        my_dbg() << "F: " << F << "\n";
    }

    return llvm::PreservedAnalyses::none();
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo()
{
    using namespace llvm;
    return {LLVM_PLUGIN_API_VERSION, "if-zero-opt", LLVM_VERSION_STRING, [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, llvm::FunctionPassManager &PM, ArrayRef<llvm::PassBuilder::PipelineElement>) {
                        // if (Name == "if-zero-opt")
                        {
                            PM.addPass(IfZeroOpt());
                            return true;
                        }
                        return false;
                    });

                PB.registerVectorizerStartEPCallback(
                    [](llvm::FunctionPassManager &FPM, llvm::OptimizationLevel O) { FPM.addPass(IfZeroOpt()); });
            }};
}