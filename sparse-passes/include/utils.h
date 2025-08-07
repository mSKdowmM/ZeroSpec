#pragma once
#include <stddef.h>
#include <array>
#include <stdexcept>
template <typename T>
struct to_range
{
    T range;
    to_range(T _range)
    : range(_range)
    {
    }
    auto begin() const
    {
        auto [b, e] = range;
        return b;
    }
    auto end() const
    {
        auto [b, e] = range;
        return e;
    }
};

template <typename T, typename... Args>
class spanND
{
private:
    T *data;
    size_t _dims[sizeof...(Args)];

public:
    spanND(T *_data, Args... dims)
    : data(_data)
    , _dims{dims...}
    {
    }
    T &operator()(Args... pos)
    {
        size_t index = 0;
        std::array<size_t, sizeof...(Args)> indices = {pos...};
        size_t stride = 1;
        for (int i = sizeof...(Args) - 1; i >= 0; --i)
        {
            if (indices[i] >= _dims[i])
            {
                throw std::out_of_range("Index out of range");
            }
            index += indices[i] * stride;
            stride *= _dims[i];
        }
        return data[index];
    }
    const T &operator()(Args... pos) const { return const_cast<spanND<T, Args...> *>(this)->operator()(pos...); }
};
template <typename T>
using span2d = spanND<T, size_t, size_t>;