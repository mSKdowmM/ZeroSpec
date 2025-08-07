#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/ExecutionEngine/Orc/ThreadSafeModule.h"
#include <algorithm>
#include <cassert>
#include <cstdio>
#include <fcntl.h>
#include <llvm/IR/Attributes.h>
#include <sys/file.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalValue.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <ZeroBenefitAnalysis.h>
#include <llvm/IR/Type.h>
#include <llvm/Support/Debug.h>
#include <memory>
#include <vector>
#include "llvm/Support/TargetSelect.h"
#include "llvm/TargetParser/Host.h"

void fill_random_bit(char *buffer, size_t size)
{
    for (size_t i = 0; i < size; ++i)
    {
        buffer[i] = rand() % 256;
    }
}

unsigned long var2long(char *ptr, int size)
{
    if (size == 4)
    {
        return *(unsigned int *)ptr;
    }
    if (size == 8)
    {
        return *(unsigned long *)ptr;
    }
    if (size == 2)
    {
        return *(unsigned short *)ptr;
    }
    if (size == 1)
    {
        return *(unsigned char *)ptr;
    }
    assert(0);
}

using namespace llvm;
using std::vector;

enum FUNC_ARGS_MODE
{
    INIT = -3,
    NONE = -2,
    ZERO = -1,
};

void testFunction(Function &func)
{
    llvm::InitializeNativeTarget();
    llvm::InitializeNativeTargetAsmPrinter();
    llvm::InitializeNativeTargetAsmParser();
    llvm::orc::LLJITBuilder builder;
    auto _context = std::make_unique<llvm::LLVMContext>();
    auto _module = std::make_unique<llvm::Module>("", *_context);
    auto threadSafeModule = llvm::orc::ThreadSafeModule(std::move(_module), std::move(_context));

    auto module = threadSafeModule.getModuleUnlocked();
    auto context = threadSafeModule.getContext().getContext();
    Intrinsic::ID id = Intrinsic::fmuladd;
    // Function *_func = Intrinsic::getDeclaration(module, id, Type::getFloatTy(*context));
    // auto &func = *_func;
    my_dbg() << "func: " << func << "\n";

    size_t args_size = 0;
    std::vector<size_t> args_offset;
    for (auto &arg : func.args())
    {
        args_offset.push_back(args_size);
        if (arg.getType()->isVectorTy())
        {
            return;
        }
        if (arg.hasAttribute(llvm::Attribute::ImmArg))
        {
            return;
        }
        auto arg_size = arg.getType()->getPrimitiveSizeInBits() / 8;
        arg_size = std::min(arg_size, 4ul);
        args_size += arg_size;
    }
    // args_offset.push_back(args_size);
    char args_buffer[args_size];

    llvm::FunctionType *wrapper_type = llvm::FunctionType::get(llvm::Type::getInt64Ty(*context),
                                                               {
                                                                //    llvm::Type::getInt32PtrTy(*context),
                                                                llvm::PointerType::get(llvm::Type::getInt32Ty(*context), 0),
                                                               },
                                                               false);
    auto wrapper_func =
        llvm::Function::Create(wrapper_type, Function::ExternalLinkage, "func", threadSafeModule.getModuleUnlocked());
    auto entry = BasicBlock::Create(func.getContext(), "entry", wrapper_func);
    SmallVector<llvm::Value *> args;
    for (auto [i, arg_offset] : enumerate(args_offset))
    {
        auto arg = llvm::ConstantInt::get(llvm::Type::getInt32Ty(func.getContext()), arg_offset);
        // auto gep = llvm::GetElementPtrInst::CreateInBounds(
        //     func.getArg(i)->getType(), warpper_func->getArg(0), arg, "gep", entry);
        auto gep = llvm::GetElementPtrInst::CreateInBounds(
            llvm::Type::getInt8Ty(*context), wrapper_func->getArg(0), arg, "gep", entry);
        llvm::LoadInst *load;
        llvm::Value *v;
        if (func.getArg(i)->getType()->isFloatTy() || func.getArg(i)->getType()->isDoubleTy())
        {
            load = new llvm::LoadInst(func.getArg(i)->getType(), gep, "load", entry);
            v = load;
        }
        else if (func.getArg(i)->getType()->isIntegerTy() && func.getArg(i)->getType()->getIntegerBitWidth() < 64)
        {
            load = new llvm::LoadInst(llvm::Type::getInt32Ty(*context), gep, "load", entry);
            if (func.getArg(i)->getType()->getIntegerBitWidth() == 1)
            {
                v = llvm::TruncInst::CreateIntegerCast(load, Type::getInt1Ty(*context), false, "", entry);
            }
            else if (func.getArg(i)->getType()->getIntegerBitWidth() == 8)
            {
                v = llvm::TruncInst::CreateIntegerCast(load, Type::getInt8Ty(*context), false, "", entry);
            }
            else if (func.getArg(i)->getType()->getIntegerBitWidth() == 16)
            {
                v = llvm::TruncInst::CreateIntegerCast(load, Type::getInt16Ty(*context), false, "", entry);
            }
            else
            {
                v = load;
            }
        }
        else
        {
            load = new llvm::LoadInst(llvm::Type::getInt64Ty(*context), gep, "load", entry);
            v = load;
        }
        args.push_back(v);
    }

    auto *call = CallInst::Create(&func, args, "", entry);
    Value *v = call;
    if (v->getType()->isFloatTy())
    {
        v = CastInst::CreateZExtOrBitCast(v, Type::getInt32Ty(*context), "", entry);
    }
    if (v->getType()->isDoubleTy())
    {
        v = CastInst::CreateTruncOrBitCast(v, Type::getInt64Ty(*context), "", entry);
    }
    if (v->getType()->isIntegerTy() && v->getType()->getIntegerBitWidth() < 64)
    {
        v = CastInst::CreateZExtOrBitCast(v, Type::getInt64Ty(*context), "", entry);
    }
    auto *ret = ReturnInst::Create(func.getContext(), v, entry);
    // auto *ret = ReturnInst::Create(func.getContext(), args[1], entry);

    my_dbg() << "warpper_func: " << *wrapper_func << "\n";

    // 创建 JITTargetMachineBuilder
    auto _JTMB = llvm::orc::JITTargetMachineBuilder::detectHost();
    if (!_JTMB)
    {
        my_dbg() << _JTMB.takeError();
    }
    auto JTMB = _JTMB.get();
    auto jit_builder = orc::LLJITBuilder();
    jit_builder.setJITTargetMachineBuilder(JTMB);
    auto jit = jit_builder.create();
    if (!jit)
    {
        my_dbg() << jit.takeError();
    }
    jit.get()->addIRModule(std::move(threadSafeModule));
    my_dbg() << "before loopup\n";
    auto _sym = (jit.get()->lookup("func"));
    my_dbg() << "after loopup\n";
    // auto sym = cantFail(jit.get()->lookup("func"));
    if (!_sym)
    {
        my_dbg() << _sym.takeError();
    }
    auto sym = _sym.get();
    auto *fnPtr = (unsigned long (*)(char *))sym.getValue();

    int zero_sensitive_args[func.arg_size()];
    std::fill_n(zero_sensitive_args, func.arg_size(), INIT);
    for (int test_target = 0; test_target < func.arg_size(); ++test_target)
    {
        int mode = INIT;
        for (int i = 0; i < 100; ++i)
        {
            for (int j = 0; j < func.arg_size(); ++j)
            {
                fill_random_bit(args_buffer + args_offset[j], func.getArg(j)->getType()->getPrimitiveSizeInBits() / 8);
            }
            memset(args_buffer + args_offset[test_target],
                   0,
                   func.getArg(test_target)->getType()->getPrimitiveSizeInBits() / 8);
            auto res = fnPtr(args_buffer);

            if (res == 0)
            {
                if (mode == INIT || mode == ZERO)
                {
                    mode = ZERO;
                    continue;
                }
            }

            for (int j = 0; j < func.arg_size(); ++j)
            {
                if (res ==
                    var2long(args_buffer + args_offset[j], func.getArg(j)->getType()->getPrimitiveSizeInBits() / 8))
                {
                    if (mode != j && mode != INIT)
                    {
                        mode = NONE;
                        break;
                    }
                    else
                    {
                        mode = j;
                    }
                }
            }
            if (mode == NONE)
            {
                break;
            }
        }
        zero_sensitive_args[test_target] = mode;
    }

    FILE *fp = fopen("zero_candidate_func", "a");
    flock(fileno(fp), LOCK_EX);
    fprintf(fp, "%s", func.getName().str().c_str());
    for (int i = 0; i < func.arg_size(); ++i)
    {
        fprintf(fp, " %d", zero_sensitive_args[i]);
    }
    fprintf(fp, "\n");
    flock(fileno(fp), LOCK_UN);
    fclose(fp);
}
