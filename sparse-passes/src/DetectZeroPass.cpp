#include <chrono>
#include "llvm/IR/Module.h"
#include "ZeroBenefitAnalysis.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Passes/PassBuilder.h"
#include <llvm/IR/Argument.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/Support/Casting.h>
#include <sys/file.h>
#include "llvm/Passes/PassPlugin.h"
#include "InstDestClassification.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/LCSSA.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Support/raw_ostream.h"
#include <assert.h>
#include <unordered_map>
#include <vector>
#include <string>
#include <atomic>
#include <filesystem>
#include <DetectZeroPass.h>
#include <probe.h>
#include <fmt/format.h>
#include <cstdlib>
#include "developing.h"
#include "userop.h"
using std::atomic_int;
using std::string;
using std::unordered_map;
using std::vector;
using std::string_view;
using namespace llvm;

const char *ZEROSPEC_INFO_ROOT = getenv("ZERO_SPEC_INFO_ROOT") ? getenv("ZERO_SPEC_INFO_ROOT") : "";

static std::string getUniqueFuncName(VectorType *VecTy)
{
    std::string Name = INSTRUMENTATION_PREFIX_STR "_check_zero_vec_";
    raw_string_ostream RSO(Name);
    RSO << (VecTy->isScalableTy() ? "sve" : "fixed");
    RSO << "_" << VecTy->getElementType()->getTypeID();
    RSO << "_" << VecTy->getElementCount().getKnownMinValue();
    RSO << "_" << VecTy->getElementType()->getScalarSizeInBits();
    return RSO.str();
}

Function *getOrCreateZeroCheckFunc(Module &M, VectorType *VecTy)
{
    LLVMContext &Ctx = M.getContext();
    std::string Name = getUniqueFuncName(VecTy);

    if (Function *F = M.getFunction(Name))
    {
        return F;
    }

    Type *RetTy = Type::getVoidTy(Ctx);
    Type *i32Ty = Type::getInt32Ty(Ctx);
    FunctionType *FuncTy = FunctionType::get(RetTy, {VecTy, i32Ty, i32Ty}, false);
    Function *F = Function::Create(FuncTy, Function::InternalLinkage, Name, &M);

    BasicBlock *BB = BasicBlock::Create(Ctx, "entry", F);
    IRBuilder<> B(BB);

    Argument *Arg = F->getArg(0);
    Value *Zero = Constant::getNullValue(VecTy);

    Value *Cmp = nullptr;
    if (VecTy->getElementType()->isFloatingPointTy())
    {
        Cmp = B.CreateFCmpOEQ(Arg, Zero, "fcmp");
    }
    else
    {
        Cmp = B.CreateICmpEQ(Arg, Zero, "icmp");
    }

    if (Cmp->getType()->isVectorTy())
    {
        Function *ReduceAnd = Intrinsic::getDeclaration(&M, Intrinsic::vector_reduce_and, {Cmp->getType()});
        Cmp = B.CreateCall(ReduceAnd, {Cmp}, "reduce");
    }

    FunctionCallee Logger = M.getOrInsertFunction(
        INSTRUMENTATION_PREFIX_STR "_record_vector_zero",
        FunctionType::get(llvm::Type::getVoidTy(Ctx),
                          {B.getInt1Ty(), llvm::Type::getInt32Ty(Ctx), llvm::Type::getInt32Ty(Ctx)},
                          false));

    // 调用 logger
    B.CreateCall(Logger, {Cmp, F->getArg(1), F->getArg(2)});

    B.CreateRetVoid();
    return F;
}

string &replace_all(string &str, std::string_view old_value, std::string_view new_value)
{
    while (true)
    {
        string::size_type pos(0);
        if ((pos = str.find(old_value)) != string::npos)
        {
            str.replace(pos, old_value.length(), new_value);
        }
        else
        {
            break;
        }
    }
    return str;
}

class Helper
{
    string value_name(const GetElementPtrInst *gep)
    {
        string ptr_name = value_name(gep->getOperand(0));
        string offset_name = "";
        for (int i = 1; i < gep->getNumOperands(); ++i)
        {
            offset_name += "[" + value_name(gep->getOperand(i)) + "]";
        }
        return ptr_name + offset_name;
    }
    string value_name(const LoadInst *load) { return value_name(load->getOperand(0)); }
    string opcode2str(unsigned opcode)
    {
        switch (opcode)
        {
        case BinaryOperator::Add:
        case BinaryOperator::FAdd:
            return "+";
        case BinaryOperator::Mul:
        case BinaryOperator::FMul:
            return "*";
        case BinaryOperator::Sub:
        case BinaryOperator::FSub:
            return "-";
        case BinaryOperator::SDiv:
        case BinaryOperator::UDiv:
        case BinaryOperator::FDiv:
            return "/";
        case BinaryOperator::Or:
            return "|";
        case BinaryOperator::And:
            return "&";
        case BinaryOperator::Shl:
            return "<<";
        case BinaryOperator::AShr:
            return ">>>";
        case BinaryOperator::LShr:
            return ">>";
        default:
            break;
        }
        my_dbg() << "unknown operator " << opcode << "\n";
        return "unknown";
    }
    string value_name(const BinaryOperator *binary)
    {
        return "(" + value_name(binary->getOperand(0)) + opcode2str(binary->getOpcode()) +
               value_name(binary->getOperand(1)) + ")";
    }
    string value_name(const Argument *arg) { return string(arg->getName()); }
    string value_name(const ConstantInt *con) { return std::to_string(con->getSExtValue()); }
    string value_name(const SExtInst *ext) { return value_name(ext->getOperand(0)); }
    string value_name(const TruncInst *trunc) { return value_name(trunc->getOperand(0)); }
    string value_name(const PHINode *phi) { return string(phi->getName()); }
    string value_name(const Value *val)
    {
#define DISPATCH(T)                                                                                                    \
    if (auto v = dyn_cast<T>(val))                                                                                     \
        return value_name(v);
        DISPATCH(LoadInst)
        DISPATCH(GetElementPtrInst)
        DISPATCH(BinaryOperator)
        DISPATCH(Argument);
        DISPATCH(ConstantInt);
        DISPATCH(SExtInst);
        DISPATCH(TruncInst);

        auto iter = metadata_map.find(val);
        if (iter != metadata_map.end())
        {
            return string(iter->second->getName());
        }
        DISPATCH(PHINode);
        my_dbg() << *val << "\n";
        my_dbg() << "no match dispatcher\n";
        return "null";

#undef DISPATCH
        // Value* ptr = load->getOperand(0);
        // if (auto gep = dyn_cast<GetElementPtrInst>(ptr))
        // {

        // }
    }
    unordered_map<const Value *, const DILocalVariable *> metadata_map;
};

PreservedAnalyses DetectZeroPass::_run(Function &F, FunctionAnalysisManager &AM)
{
    if (F.hasFnAttribute("zero-instrumented"))
    {
        return PreservedAnalyses::all();
    }
    F.addFnAttr("zero-instrumented");

    if (auto target_func_name = getenv("DETECT_TARGET_FUNC"))
    {
        if (F.getName() != target_func_name)
        {
            return PreservedAnalyses::all();
        }
    }
    // if (F.getName().contains(INSTRUMENTATION_PREFIX) || F.getName().starts_with("_ZNSt"))
    if (F.getName().contains(INSTRUMENTATION_PREFIX_STR))
    {
        return PreservedAnalyses::all();
    }
    DISubprogram *subprogram_for_F = nullptr;
    for (auto &bb : F)
    {
        for (auto &inst : bb)
        {
            auto di = inst.getDebugLoc().get();
            if (di && di->getScope() && di->getScope()->getSubprogram() &&
                (di->getScope()->getSubprogram()->getLinkageName() == F.getName() ||
                 di->getScope()->getSubprogram()->getName() == F.getName()))
            {
                subprogram_for_F = di->getScope()->getSubprogram();
            }
            if (subprogram_for_F)
            {
                break;
            }
        }
        if (subprogram_for_F)
        {
            break;
        }
    }
    if (!subprogram_for_F)
    {
        return PreservedAnalyses::all();
    }

    std::string info_path = (std::string(ZEROSPEC_INFO_ROOT) + "/" +
                             std::filesystem::absolute(F.getParent()->getSourceFileName()).string() + ".info");
    if (!std::filesystem::exists(info_path))
    {
        std::filesystem::path p(info_path);
        std::filesystem::create_directories(p.parent_path());
    }
    FILE *f_dbg_info = fopen((std::string(ZEROSPEC_INFO_ROOT) + "/" +
                              std::filesystem::absolute(F.getParent()->getSourceFileName()).string() + ".info")
                                 .c_str(),
                             "a+");
    if (!f_dbg_info)
    {
        my_dbg() << "failed to open file" << F.getParent()->getSourceFileName() << ".info\n";
        exit(-1);
    }
    my_dbg() << "-------------------------------------------------------\n";
    my_dbg() << "func name: " << F.getName() << "\n";

    LCSSAPass().run(F, AM);
    auto loop_info = LoopAnalysis().run(F, AM);
    auto st = std::chrono::high_resolution_clock::now();
    auto benefit = ZeroBenefitAnalysis().run(F, AM);
    auto ed = std::chrono::high_resolution_clock::now();
    fprintf(stderr,
            "[ZeroBenefitAnalysis] time: %ld\n",
            std::chrono::duration_cast<std::chrono::milliseconds>(ed - st).count());

    AM.invalidate(F, PreservedAnalyses::all());

    int inst_id = 0;
    LLVMContext &C = F.getContext();
    Module &M = *F.getParent();
    // my_dbg() << "module_name: " << F.getParent()->getName() << "\n";
    // std::vector<int8_t> name_vec;
    // auto func_name_str = F.getName().str();
    // name_vec.insert(name_vec.end(), func_name_str.begin(), func_name_str.end());
    // name_vec.push_back('\0');
    auto func_name = subprogram_for_F->getName().str();
    auto func_linkage_name = subprogram_for_F->getLinkageName().str();
    auto func_name_ptr = func_linkage_name == "" ? func_name.c_str() : func_linkage_name.c_str();
    auto loc_name_maybe_relative = M.getSourceFileName();
    auto loc_name = std::filesystem::absolute(loc_name_maybe_relative).string() + ":" + func_name_ptr;
    auto loc_name_ir = ConstantDataArray::getString(C, loc_name.c_str());
    auto loc_name_val =
        new GlobalVariable(*F.getParent(), loc_name_ir->getType(), true, GlobalValue::PrivateLinkage, loc_name_ir);
    /*
                for (auto &bb : F)
                {
                    for (auto &inst : bb)
                    {
                        // my_dbg()<<"-----------\n";
                        // my_dbg()<<inst<<"\n";
                        // // auto di = inst.getDebugLoc().get();
                        // SmallVector<std::pair<unsigned, MDNode *>> mds;
                        // inst.getAllMetadata(mds);
                        // for (auto& md: mds)
                        // {
                        //     my_dbg()<<*md.second<<"\n";
                        // }

                        // for (auto user: metadata_val->users())
                        // {
                        //     if (const auto call = dyn_cast<CallInst>(user))
                        //     {
                        //         auto callee_name = cast<Function>(call->getCalledOperand())->getName();
                        //         if (callee_name.contains("llvm.dbg"))
                        //         {
                        //             my_dbg()<<"-----------------\n";
                        //             my_dbg()<<*call<<"\n";
                        //             // auto metadata = ConstantAsMetadata(Metadata::DILocalVariableKind, call->getOperand(1));
                        //             auto metadata = cast<MetadataAsValue>(call->getOperand(1));
                        //             auto dilv = cast<DILocalVariable>(metadata->getMetadata());
                        //             my_dbg()<<*call->getOperand(0)<<"\n";
                        //             my_dbg()<<dilv->getName()<<"\n";
                        //         }

                        //     }
                        // }

                        // if (di != nullptr)
                        // {
                        //     my_dbg()<<*di<<"\n";
                        // }
                        // my_dbg()<<inst.getOpcodeName()<<"\n";
                        if (const auto call = dyn_cast<CallInst>(&inst))
                        {
                            auto callee_name = cast<Function>(call->getCalledOperand())->getName();
                            if (callee_name.contains("llvm.dbg.value"))
                            {
                                // my_dbg()<<"-----------------\n";
                                // my_dbg()<<*call<<"\n";
                                // auto metadata = ConstantAsMetadata(Metadata::DILocalVariableKind, call->getOperand(1));
                                auto metadata = cast<MetadataAsValue>(call->getOperand(1));
                                auto dilv = cast<DILocalVariable>(metadata->getMetadata());
                                auto metadata0 = cast<MetadataAsValue>(call->getOperand(0));
                                // auto val = (static_cast<ValueAsMetadata*>(metadata0->getMetadata()))->getValue();
                                if (!metadata0->getMetadata())
                                    continue;
                                my_dbg() << *metadata0 << "\n";
                                auto val = (cast<ValueAsMetadata>(metadata0->getMetadata()))->getValue();

                                if (isa<Instruction, Argument>(val))
                                {
                                    metadata_map.emplace(val, dilv);
                                }
                                // assert((isa<Argument, Instruction, Constant>(val)));
                                // my_dbg()<<*val<<"\n";
                                // my_dbg()<<dilv->getName()<<"\n";
                            }
                        }
                        // my_dbg()<<"-----------------\n";
                        // my_dbg()<<inst<<"\n";
                        // for (const auto& user: inst.users())
                        // {
                        //     my_dbg()<<user;
                        // }
                    }
                }
        */
    vector<Value *> instrument_target;
    for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg)
    {
        instrument_target.push_back(&*arg);
    }
    /*
        for (auto &bb : F)
        {
            for (auto &inst : bb)
            {
                if (auto load = dyn_cast<LoadInst>(&inst))
                {
                    auto load_target = load->getOperand(0);
                    my_dbg() << "load: " << *load << *load->getType() << "\n";
                    if (auto gep = dyn_cast<GetElementPtrInst>(load_target))
                    {
                        auto ptr = gep->getOperand(0);
                        if (isa<Argument, Instruction>(ptr))
                        {
                            instrument_target.push_back(load);
                        }
                        else
                        {
                            my_dbg() << "ptr: " << *ptr << "\n";
                        }
                    }
                    else
                    {
                        my_dbg() << "load target: " << *load_target << "\n";
                    }
                }
            }
        }
*/

    // auto &res = AM.getResult<InstDestClassification>(F);
    auto res = InstDestClassification().run(F, AM);
    for (const auto [v, type] : res.value2type)
    {
        if (!v)
        {
            continue;
        }
        if (auto inst = dyn_cast<Instruction>(v))
        {
            if (type & InstDestClassificationResult::VALUE_TYPE)
            {
                instrument_target.push_back(inst);
            }
            // my_dbg() << *inst << ": " << type << "\n";
        }
    }

    auto buffer_allocator_type =
        FunctionType::get(Type::getInt32Ty(C), {PointerType::get(Type::getInt8Ty(C), 0), Type::getInt32Ty(C)}, false);
    Function *buffer_allocator = M.getFunction(INSTRUMENTATION_PREFIX_STR ALLOCATE_BUFFER_PREFIX);
    if (!buffer_allocator)
    {
        // assert(false);
        buffer_allocator = Function::Create(buffer_allocator_type,
                                            GlobalValue::LinkageTypes::ExternalLinkage,
                                            INSTRUMENTATION_PREFIX_STR ALLOCATE_BUFFER_PREFIX,
                                            M);
    }

    auto allocate_buffer =
        CallInst::Create(buffer_allocator_type,
                         buffer_allocator,
                         {loc_name_val, ConstantInt::get(Type::getInt32Ty(C), instrument_target.size(), true)});
    allocate_buffer->insertBefore(&*F.getEntryBlock().getFirstNonPHIOrDbgOrAlloca());
    if (subprogram_for_F)
    {
        allocate_buffer->setDebugLoc(DebugLoc(DILocation::get(C, 0, 0, subprogram_for_F)));
    }
    // allocate_buffer->setDebugLoc(DebugLoc());
    // vector<Type *> func_params = vector<Type *>({Type::getDoubleTy(C)});
    // FunctionType *func_type = FunctionType::get(Type::getVoidTy(C), func_params, false);

    // Function *instrumentation = Function::Create(func_type,
    //                                              GlobalValue::LinkageTypes::ExternalLinkage,
    //                                              "instrumentation0", F.getParent());
    unordered_map<Type *, Function *> func_map;
    auto function_creator = [&](Type *type, const string &name) {
        // vector<Type *> func_params = vector<Type *>{type, Type::getInt32Ty(C), Type::getInt32Ty(C)};
        if (auto res = M.getFunction(name))
        {
            return res;
        }
        else
        {
            // assert(false);
            vector<Type *> func_params = vector<Type *>{type, Type::getInt32Ty(C), Type::getInt32Ty(C)};
            FunctionType *func_type = FunctionType::get(Type::getVoidTy(C), func_params, false);
            return Function::Create(func_type, GlobalValue::LinkageTypes::ExternalLinkage, name, F.getParent());
        }
    };
    func_map.emplace(Type::getDoubleTy(C),
                     function_creator(Type::getDoubleTy(C), INSTRUMENTATION_PREFIX_STR CHECK_ZERO_PREFIX "double"));
    func_map.emplace(Type::getFloatTy(C),
                     function_creator(Type::getFloatTy(C), INSTRUMENTATION_PREFIX_STR CHECK_ZERO_PREFIX "float"));
    func_map.emplace(Type::getInt32Ty(C),
                     function_creator(Type::getInt32Ty(C), INSTRUMENTATION_PREFIX_STR CHECK_ZERO_PREFIX "int"));
    func_map.emplace(Type::getInt64Ty(C),
                     function_creator(Type::getInt64Ty(C), INSTRUMENTATION_PREFIX_STR CHECK_ZERO_PREFIX "int64_t"));
    func_map.emplace(Type::getInt8Ty(C),
                     function_creator(Type::getInt8Ty(C), INSTRUMENTATION_PREFIX_STR CHECK_ZERO_PREFIX "int8_t"));
    func_map.emplace(Type::getInt16Ty(C),
                     function_creator(Type::getInt16Ty(C), INSTRUMENTATION_PREFIX_STR CHECK_ZERO_PREFIX "int16_t"));
    func_map.emplace(Type::getInt1Ty(C),
                     function_creator(Type::getInt1Ty(C), INSTRUMENTATION_PREFIX_STR CHECK_ZERO_PREFIX "int1_t"));
    int ZERO_BENEFIT_THRESHOLD = 0;
    if (getenv("ZERO_BENEFIT_THRESHOLD"))
    {
        ZERO_BENEFIT_THRESHOLD = std::stoi(getenv("ZERO_BENEFIT_THRESHOLD"));
    }
    vector<string> dbg_info_v;
    for (const auto v : instrument_target)
    {
        if (benefit[v] < ZERO_BENEFIT_THRESHOLD)
        {
            continue;
        }
        auto inst = dyn_cast<Instruction>(v);
        auto inst_type = v->getType();
        auto iter = func_map.find(inst_type);
        // if (isa<InvokeInst>(inst))
        // {
        //     continue;
        // }
        if (inst_type->isPointerTy())
        {
            continue;
        }
        llvm::Function *instrumentation = nullptr;
        if (iter == func_map.end())
        {
            if (inst_type->isVectorTy() && !inst_type->isPtrOrPtrVectorTy())
            {
                instrumentation = getOrCreateZeroCheckFunc(M, llvm::cast<VectorType>(inst_type));
            }
            else
            {
                my_dbg() << "-----------------------\n";
                my_dbg() << "unknown inst type: " << *inst_type << " for inst " << *v << "\n";
                continue;
            }
        }
        else
        {
            instrumentation = iter->second;
        }

        // if (benefit[inst] <= 0)
        // {
        //     continue;
        // }
        auto func_type = instrumentation->getFunctionType();
        auto di = inst ? inst->getDebugLoc().get() : nullptr;
        if (!di)
        {
            my_dbg() << "check instrumentation target " << *v << "\n";
        }
        int line = di ? di->getLine() : -1;
        int column = di ? di->getColumn() : -1;
        auto scope = di ? di->getScope() : nullptr;
        auto subprogram = scope ? scope->getSubprogram() : nullptr;
        auto linkage_name = subprogram ? subprogram->getLinkageName().str() : F.getName().str();
        replace_all(linkage_name, ":", "$");
        auto raw_name = subprogram ? subprogram->getName().str() : F.getName().str();
        replace_all(raw_name, ":", "$");
        auto real_source = di ? (di->getDirectory() + "/" + (di->getFilename())).str() : "";
        auto info = fmt::format(
            "{}:{}:{}:{}:{}:{}:{}\n", inst_id, line, column, linkage_name, raw_name, real_source, benefit[v]);
        my_dbg() << "benefit " << benefit[v] << " of inst " << *v << "\n";

        if (di && di->getScope() && di->getScope()->getSubprogram())
        {
            v->getName();
            my_dbg() << "target " << *v << *di->getScope()->getSubprogram() << " at line " << line << "\n";
        }
        // my_dbg() << "type: " << *func_name->getType()->getScalarType() << "\n";
        // auto func_name_ptr = GetElementPtrInst::Create(
        //     func_name->getType()->getArrayElementType(), func_name, {0}
        // );
        // func_name_ptr->insertAfter(load);
        // my_dbg()<<"func name ptr: "<<*func_name_ptr<<"\n";

        vector<Value *> args = vector<Value *>{
            v,
            // func_name_ptr,
            // func_name_val,
            allocate_buffer,
            ConstantInt::get(Type::getInt32Ty(C), inst_id++, true),
        };
        auto call = CallInst::Create(func_type, instrumentation, args);
        if (auto phi = dyn_cast<PHINode>(v))
        {
            call->insertBefore(&*phi->getParent()->getFirstInsertionPt());
        }
        else if (auto invoke = dyn_cast<InvokeInst>(v))
        {
            if (invoke->getNormalDest()->getSinglePredecessor())
            {
                call->insertBefore(invoke->getNormalDest()->getFirstNonPHI());
            }
            else
            {
                inst_id--;
                call->deleteValue();
                continue;
            }
        }
        else if (auto arg = dyn_cast<Argument>(v))
        {
            call->insertAfter(allocate_buffer);
        }
        else
        {
            call->insertAfter(inst);
        }
        // if (di)
        // {
        //     call->setDebugLoc(DebugLoc(DILocation::get(C, 0, 0, di->getScope())));
        // }
        if (subprogram_for_F)
        {
            call->setDebugLoc(DebugLoc(DILocation::get(C, 0, 0, subprogram_for_F)));
        }
        dbg_info_v.push_back(std::move(info));
        // my_dbg()<<"-------------\n";
        // my_dbg()<<load<<"\n";
    }
    allocate_buffer->setArgOperand(1, ConstantInt::get(Type::getInt32Ty(C), inst_id, true));
    my_dbg() << "finish instrumentation\n";
    auto define_file_name = (subprogram_for_F->getDirectory() + "/" + subprogram_for_F->getFilename()).str();
    auto valid_func_linkage_name = func_linkage_name;
    replace_all(valid_func_linkage_name, ":", "$");
    auto valid_func_name = func_name;
    replace_all(valid_func_name, ":", "$");
    auto function_desc_str =
        fmt::format("[FUNCTION]:{}:{}:{}\n", valid_func_name, valid_func_linkage_name, define_file_name);
    flock(fileno(f_dbg_info), LOCK_EX);
    // fputs("[FUNCTION]:", f_dbg_info);
    // fputs(func_name.c_str(), f_dbg_info);
    // fputs(":", f_dbg_info);
    // fputs(func_linkage_name.c_str(), f_dbg_info);
    // fputs(":", f_dbg_info);
    // // fputs(loc_name.c_str(), f_dbg_info);
    // F.getSubprogram()->getFilename();
    // fputs("\n", f_dbg_info);
    fputs(function_desc_str.c_str(), f_dbg_info);
    for (auto &info : dbg_info_v)
    {
        fputs(info.c_str(), f_dbg_info);
    }
    flock(fileno(f_dbg_info), LOCK_UN);
    fclose(f_dbg_info);

    if (getenv("DUMP_FUNC"))
    {
        my_dbg() << "dump func: " << F << "\n";
    }

    return PreservedAnalyses::none();
}
PreservedAnalyses DetectZeroPass::run(Function &F, FunctionAnalysisManager &AM)
{
    if (auto target_func_name = getenv("DETECT_TARGET_FUNC"))
    {
        if (F.getName() != target_func_name)
        {
            return PreservedAnalyses::all();
        }
    }
    int instr_count = 0;
    for (auto &bb : F)
    {
        for (auto &instr : bb)
        {
            ++instr_count;
        }
    }
    fprintf(stderr, "[INSTR_COUNT]: %d\n", instr_count);
    auto res = _run(F, AM);

    std::vector<UserOp2Inst *> op2s;
    for (auto &bb : F)
    {
        for (auto &inst : bb)
        {
            for (auto user : inst.users())
            {
                if (auto op = dyn_cast<UserOp2Inst>(user))
                {
                    op2s.push_back(op);
                }
            }
        }
    }
    for (auto op : op2s)
    {
        op->setOperand(0, nullptr);
    }
    return res;
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo()
{
    return {LLVM_PLUGIN_API_VERSION, "DetectZero", LLVM_VERSION_STRING, [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, llvm::FunctionPassManager &PM, ArrayRef<llvm::PassBuilder::PipelineElement>) {
                        if (Name == "detect-zero")
                        {
                            PM.addPass(DetectZeroPass());
                            return true;
                        }
                        return false;
                    });
                PB.registerVectorizerStartEPCallback(
                    [](llvm::FunctionPassManager &FPM, llvm::OptimizationLevel O) { FPM.addPass(DetectZeroPass()); });
                PB.registerAnalysisRegistrationCallback(
                    [](FunctionAnalysisManager &AM) { AM.registerPass([&] { return InstDestClassification(); }); });
            }};
}
