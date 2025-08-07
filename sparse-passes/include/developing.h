#pragma once
#include "userop.h"
#include <llvm/IR/Function.h>
#include <llvm/IR/Use.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/Verifier.h>
#include <type_traits>
class DummyOutput
{
};

template <typename T>
DummyOutput &operator<<(DummyOutput &out, T &&value)
{
    return out;
}
template <typename T>
DummyOutput &operator<<(DummyOutput &out, const T &value)
{
    return out;
}

inline bool my_dbg_enabled = []() {
    if (getenv("ZERO_SPEC_DBG"))
    {
        return true;
    }
    else
    {
        return false;
    }
}();

class _my_dbg
{
public:
    decltype(llvm::dbgs()) dbgs_handle = llvm::dbgs();
};
template <typename T>
_my_dbg &operator<<(_my_dbg &out, T &&value)
{
#ifndef ZERO_SPEC_DISABLE_DBG
    if (!my_dbg_enabled)
    {
        return out;
    }
    if constexpr (std::is_same_v<T, llvm::Value> || std::is_base_of_v<llvm::Value, T>)
    {
        if (llvm::isa<llvm::UserOp2Inst>(value))
        {
            out.dbgs_handle << "userop2\n";
        }
        else
        {
            out.dbgs_handle << value;
        }
    }
    else
    {
        out.dbgs_handle << value;
    }
#endif
    return out;
}
template <typename T>
_my_dbg &operator<<(_my_dbg &out, const T &value)
{
#ifndef ZERO_SPEC_DISABLE_DBG
    if (!my_dbg_enabled)
    {
        return out;
    }
    if constexpr (std::is_same_v<T, llvm::Value> || std::is_base_of_v<llvm::Value, T>)
    {
        if (llvm::isa<llvm::UserOp2Inst>(value))
        {
            out.dbgs_handle << "userop2\n";
        }
        else
        {
            out.dbgs_handle << value;
        }
    }
    else
    {
        out.dbgs_handle << value;
    }
#endif
    return out;
}

inline DummyOutput dummy_dbgs_instance;

inline DummyOutput &dummy_dbgs() { return dummy_dbgs_instance; }
inline _my_dbg _my_dbgs_instance{};

inline _my_dbg &my_dbg() { return _my_dbgs_instance; }

inline void verifyFunction(llvm::Function &F, _my_dbg &dbg)
{
    if (!my_dbg_enabled)
    {
        return;
    }
    if (llvm::verifyFunction(F, &dbg.dbgs_handle))
    {
        dbg << "verify failed\n";
    }
    else
    {
        dbg << "verify pass\n";
    }
}

#ifndef DEVELOPING
#define dbgs dummy_dbgs
#endif

#ifdef NDEBUG
#ifndef dbgs
#define dbgs dummy_dbgs
#endif
#endif
