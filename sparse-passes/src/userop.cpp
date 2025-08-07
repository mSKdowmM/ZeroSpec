#include "userop.h"
#include <mutex>
using namespace llvm;
thread_local std::vector<UserOp2Inst *> llvm::UserOp2Inst::ops;
std::mutex llvm::UserOp2Inst::mtx;