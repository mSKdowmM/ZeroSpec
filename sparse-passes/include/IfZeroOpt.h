#pragma once

#include "llvm/IR/PassManager.h"

class IfZeroOpt : public llvm::PassInfoMixin<IfZeroOpt>
{
public:
    llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);
};