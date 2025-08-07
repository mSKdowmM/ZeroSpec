#ifdef INSTRUMENTATION_HEADER
#pragma once
#endif

#include <stdio.h>
#include <atomic>
#include <unordered_map>
#include <stdlib.h>
#include <string>
#include <vector>
#include <unistd.h>
#include <sys/syscall.h>
#include <filesystem>
#include <probe.h>

#ifndef INSTRUMENTATION_HEADER
#define inline
#endif

#define __INSTRUMENTATION_CONCAT(a, b) a##b
#define INSTRUMENTATION_CONCAT(a, b) __INSTRUMENTATION_CONCAT(a, b)
#define INSTRUMENTATION_DECLARE(ret_type, name)                                                                        \
    __attribute__((used)) __attribute__((visibility("default"))) inline ret_type INSTRUMENTATION_CONCAT(               \
        INSTRUMENTATION_PREFIX, name)

namespace
{
thread_local bool valid = true;
}; // namespace
namespace INSTRUMENTATION_PREFIX
{

inline uint32_t get_tid() { return syscall(SYS_gettid); }
using namespace std;
enum ZeroType
{
    UNKNOWN = -1,
    INT = 0,
    FLOAT32 = 1,
    FLOAT64 = 2
};

template <typename T>
struct ZeroTypeHelper
{
    static constexpr ZeroType value = [] {
        if (std::is_same<T, int>::value)
        {
            return ZeroType::INT;
        }
        else if (std::is_same<T, float>::value)
        {
            return ZeroType::FLOAT32;
        }
        else if (std::is_same<T, double>::value)
        {
            return ZeroType::FLOAT64;
        }
        else
        {
            return ZeroType::INT;
        }
    }();
};
template <typename T>
ZeroType ZeroType_v = ZeroTypeHelper<T>::value;

struct ZeroInfoEntry
{
    char prediction_bits{0};
    ZeroType zero_type{ZeroType::UNKNOWN};
    uint64_t total_count{0};
    uint64_t zero_count{0};
    uint64_t predict_hit_count{0};
    ZeroInfoEntry() = default;
};
static thread_local int tid = get_tid();
struct ZeroInfo
{
    vector<ZeroInfoEntry> info;
    unordered_map<std::string, int> offset_map;
    FILE *f_zero;
    FILE *f_func_map;
    int allocate(const char *loc_name, int size)
    {
        if (size == 0)
        {
            return -1;
        }
        size_t top = info.size();
        auto [iter, new_allocated] = offset_map.try_emplace(loc_name, top);
        if (new_allocated)
        {
            info.resize(top + size);
            // printf("allocate for %d %s %d: %d\n", tid, loc_name, size, iter->second);
        }
        return iter->second;
    }

    ZeroInfo()
    {
        std::string log_prefix_path = "./";
        if (const char *env_p = std::getenv("ZERO_SPEC_LOG_PATH"))
        {
            log_prefix_path = env_p;
        }
        std::filesystem::path log_path(log_prefix_path + "/" + std::string("data-") + std::to_string(getpid()));
        if (!std::filesystem::exists(log_path))
        {
            std::filesystem::create_directory(log_path);
        }
        string f_zero_name = log_path.string() + "/" + string("zero-") + to_string(get_tid());
        string func_map_name = log_path.string() + "/" + string("func-map-") + to_string(get_tid());
        f_zero = fopen(f_zero_name.c_str(), "wb");
        f_func_map = fopen(func_map_name.c_str(), "wb");
        // printf("hello from zeroinfo\n");
    }

    ~ZeroInfo()
    {
        fprintf(f_zero, "[REPORT BEGIN]\n");
        for (auto i = 0u; i < info.size(); ++i)
        {
            fprintf(f_zero,
                    "%d %lu %lu %d %lu\n",
                    i,
                    info[i].total_count,
                    info[i].zero_count,
                    info[i].zero_type,
                    info[i].predict_hit_count);
        }
        fprintf(f_zero, "[REPORT END]\n");
        fclose(f_zero);
        fprintf(f_func_map, "[REPORT BEGIN]\n");
        for (auto iter : offset_map)
        {
            fprintf(f_func_map, "%s:%d\n", iter.first.c_str(), iter.second);
        }
        fprintf(f_func_map, "[REPORT END]\n");
        fclose(f_func_map);
        valid = false;
    }
};

thread_local ZeroInfo __zero_buffer;
thread_local ZeroInfo* p_zero_buffer = &__zero_buffer;

template <typename T>
inline void check_zero(T val, int func_id, int load_id)
{
    auto& zero_buffer = *p_zero_buffer;
    if (func_id == -1)
    {
        return;
    }
    // info.info[load_id].total_count.fetch_add(1);
    zero_buffer.info[func_id + load_id].total_count++;
    if (val == 0)
    {
        zero_buffer.info[func_id + load_id].zero_count++;
        // info.info[load_id].zero_count.fetch_add(1);
    }
    switch (zero_buffer.info[func_id + load_id].prediction_bits)
    {
    case 0:
        if (val == 0)
        {
            zero_buffer.info[func_id + load_id].predict_hit_count += 1;
        }
        else
        {
            zero_buffer.info[func_id + load_id].prediction_bits = 1;
        }
        break;
    case 1:
        if (val == 0)
        {
            zero_buffer.info[func_id + load_id].predict_hit_count += 1;
            zero_buffer.info[func_id + load_id].prediction_bits = 0;
        }
        else
        {
            zero_buffer.info[func_id + load_id].prediction_bits = 2;
        }
    case 2:
        if (val != 0)
        {
            zero_buffer.info[func_id + load_id].prediction_bits = 3;
            zero_buffer.info[func_id + load_id].predict_hit_count += 1;
        }
        else
        {
            zero_buffer.info[func_id + load_id].prediction_bits = 1;
        }
    case 3:
        if (val != 0)
        {
            zero_buffer.info[func_id + load_id].predict_hit_count += 1;
        }
        else
        {
            zero_buffer.info[func_id + load_id].prediction_bits = 2;
        }
    }
    zero_buffer.info[func_id + load_id].zero_type = ZeroType_v<T>;

    // cout << "val: " << val << " file id: " << func_id << " line: " << load_id << endl;
}

#define INSTRUMENTATION_BUILD(T)                                                                                       \
    INSTRUMENTATION_DECLARE(void, _check_zero_##T)(T val, int func_id, int load_id)                                    \
    {                                                                                                                  \
        INSTRUMENTATION_PREFIX::check_zero(val, func_id, load_id);                                                     \
    }

} // namespace INSTRUMENTATION_PREFIX
using int1_t = bool;
extern "C"
{
    INSTRUMENTATION_BUILD(double)
    INSTRUMENTATION_BUILD(int)
    INSTRUMENTATION_BUILD(float)
    INSTRUMENTATION_BUILD(int64_t)
    INSTRUMENTATION_BUILD(int8_t)
    INSTRUMENTATION_BUILD(int16_t)
    INSTRUMENTATION_BUILD(int1_t)

    INSTRUMENTATION_DECLARE(void, _record_vector_zero)(int1_t res, int func_id, int load_id)
    {
        INSTRUMENTATION_PREFIX::check_zero(!res, func_id, load_id);
    }

    INSTRUMENTATION_DECLARE(int, __allocate_zero_buffer)(const char *loc_name, int size)
    {
        if (!valid)
        {
            return -1;
        }
        return INSTRUMENTATION_PREFIX::p_zero_buffer->allocate(loc_name, size);
    }
}

#undef INSTRUMENTATION_BUILD
#undef INSTRUMENTATION_PREFIX
#undef INSTRUMENTATION_CONCAT
#undef __INSTRUMENTATION_CONCAT
#undef INSTRUMENTATION_DECLARE
