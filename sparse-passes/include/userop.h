#pragma once
#include "llvm/IR/Instructions.h"
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Value.h>
#include <mutex>
#include <unordered_map>

namespace llvm
{

class UserOp1Inst : public llvm::Instruction
{
public:
    UserOp1Inst(llvm::LLVMContext &C)
    : llvm::Instruction(Type::getVoidTy(C), llvm::Instruction::UserOp1, nullptr, 0)
    {
    }
    static UserOp1Inst *Create(llvm::LLVMContext &C) { return new UserOp1Inst(C); }
    static bool classof(const Value *V)
    {
        return V->getValueID() == (llvm::Value::InstructionVal + Instruction::UserOp1);
    }
};

class UserOp2Inst : public llvm::Instruction
{
public:
    enum Type
    {
        State,
        CloneHelper
    };
    Type _t;
    llvm::Value *zero_instr;
    UserOp2Inst(llvm::LLVMContext &C, Value *op)
    : llvm::Instruction(llvm::Type::getVoidTy(C), llvm::Instruction::UserOp2, &Op<0>(), 1)
    {
        Op<0>() = op;
    }
    static std::mutex mtx;
    static UserOp2Inst *Create(llvm::Value *op, Type t)
    {
        auto res = new UserOp2Inst(op->getContext(), op);
        res->_t = t;
        // fprintf(stderr, "create userop2inst\n");
        {
            // auto guard = std::lock_guard(mtx);
            // ops.push_back(res);
        }
        return res;
    }
    static void Destory(UserOp2Inst *inst)
    {
        // fprintf(stderr, "delete userop2inst\n");
        delete inst;
    }
    thread_local static std::vector<UserOp2Inst *> ops;
    static void Release()
    {
        for (auto op : ops)
        {
            Destory(op);
        }
        ops.clear();
    }

public:
    // allocate space for exactly one operand
    void *operator new(size_t S) { return User::operator new(S, 1); }
    void operator delete(void *Ptr) { User::operator delete(Ptr); }

    /// Transparently provide more efficient getOperand methods.
    DECLARE_TRANSPARENT_OPERAND_ACCESSORS(Value);

    // Methods for support type inquiry through isa, cast, and dyn_cast:
    static bool classof(const Value *V)
    {
        return V->getValueID() == (llvm::Value::InstructionVal + Instruction::UserOp2);
    }
    static bool classof(const Instruction *I) { return I->getOpcode() == Instruction::UserOp2; }
};
template <>
struct OperandTraits<UserOp2Inst> : public FixedNumOperandTraits<UserOp2Inst, 1>
{
};
DEFINE_TRANSPARENT_OPERAND_ACCESSORS(UserOp2Inst, Value);
} // namespace llvm