#pragma once
#include <llvm/IR/PassManager.h>
class ZeroSpecOpt : public llvm::PassInfoMixin<ZeroSpecOpt>
{
    llvm::PreservedAnalyses _run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);

public:
    llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);
};
