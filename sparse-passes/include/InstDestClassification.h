#pragma once

#include "llvm/IR/Value.h"
#include "llvm/IR/PassManager.h"
#include <unordered_map>

class InstDestClassification;
class InstDestClassificationResult
{
private:
    friend InstDestClassification;
    InstDestClassificationResult &operator=(const InstDestClassificationResult &) = delete;
    InstDestClassificationResult(const InstDestClassificationResult &) = delete;

public:
    InstDestClassificationResult() = default;
    InstDestClassificationResult(std::unordered_map<llvm::Value *, int> &&);
    enum InstType
    {
        EMPTY_TYPE = 0,
        BRANCH_TYPE = 1,
        PTR_TYPE = 2,
        VALUE_TYPE = 4,
        INDEX_TYPE = 8
    };
    InstDestClassificationResult(InstDestClassificationResult &&);
    InstDestClassificationResult &operator=(InstDestClassificationResult &&);
    static InstType getType(int id, llvm::Value *val);
    std::unordered_map<llvm::Value *, int> value2type;
};
class InstDestClassification : public llvm::AnalysisInfoMixin<InstDestClassification>
{
    friend llvm::AnalysisInfoMixin<InstDestClassification>;
    static llvm::AnalysisKey Key;

public:
    using Result = InstDestClassificationResult;
    InstDestClassificationResult run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);
};
