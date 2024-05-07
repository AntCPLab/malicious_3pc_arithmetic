#ifndef TOOLS_MYUTILS_HPP
#define TOOLS_MYUTILS_HPP

#include <queue>
#include <thread>
#include <mutex>
#include <condition_variable>

#include "Tools/Hash.h"
#include "Math/mersenne.hpp"
#include "SafeQueue.h"
#include "Math/gf2n.h"

typedef unsigned __int128 uint128_t;

class WaitSize {
public:
    WaitSize() : count(0), target(0) {}

    void set_target(int t) {
        std::unique_lock<std::mutex> lock(mutex);
        target = t;
        count = 0;
        lock.unlock();
        cv.notify_all();
    }

    void reset() {
        std::unique_lock<std::mutex> lock(mutex);
        count = 0;
        lock.unlock();
        cv.notify_all();
    }

    WaitSize& operator++() {
        std::unique_lock<std::mutex> lock(mutex);
        count++;
        if (count == target) {
            cv.notify_one();
        }
        return *this;
    }

    // wait until counter == target
    void wait() {
        std::unique_lock<std::mutex> lock(mutex);
        cv.wait(lock, [this] { return count == target; });
    }

private:
    int count; // counter
    int target; // target
    std::mutex mutex; // lock
    std::condition_variable cv; // cv
};


template <typename T1, typename T2>
struct MyPair {
public:
    T1 first;
    T2 second;

    MyPair(): first(0), second(0) {}
    MyPair(T1 a, T2 b): first(a), second(b) {}
};

class LocalHash {
    octetStream buffer;
public:

    template <typename T>
    void update(T data) {
        buffer.store(data);
    }

    gf2n_long final() {
        Hash hash;
        hash.reset();
        hash.update(buffer);
        gf2n_long result;
        hash.final().get(result);
        return result;
    }

    void append_one_msg(gf2n_long msg) {
        update(msg);
    }

    void append_msges(vector<gf2n_long> msges) {
        for(gf2n_long msg: msges) {
            update(msg);
        }
    }

    gf2n_long get_challenge() {
        gf2n_long r = final();
        return r;
    }
};

template <typename T>
class Queue {
public:
  T pop() {
    std::lock_guard<std::mutex> lock(mutex_);
    T item = queue_.front();
    queue_.pop();
    return item;
  }

  void push(const T& item) {
    std::lock_guard<std::mutex> lock(mutex_);
    queue_.push(item);
  }

  bool empty() {
    std::lock_guard<std::mutex> lock(mutex_);
    return queue_.empty();
  }

private:
  std::queue<T> queue_;
  std::mutex mutex_;
};


class DZKP_UTILS {

public:

    static void get_bases(uint64_t n, uint64_t** result) {
        for (uint64_t i = 0; i < n - 1; i++) {
            for(uint64_t j = 0; j < n; j++) {
                result[i][j] = 1;
                for(uint64_t l = 0; l < n; l++) {
                    if (l != j) {
                        uint64_t denominator, numerator;
                        if (j > l) {
                            denominator = j - l;
                        }
                        else {
                            denominator = Mersenne::neg(l - j);
                        }
                        numerator = i + n - l;
                        result[i][j] = Mersenne::mul(result[i][j], Mersenne::mul(Mersenne::inverse(denominator), numerator));
                    }
                }
            }
        }
    }

    static void evaluate_bases(uint64_t n, uint64_t r, uint64_t* result) {

        for(uint64_t i = 0; i < n; i++) {
            result[i] = 1;
            for(uint64_t j = 0; j < n; j++) {
                if (j != i) {
                    uint64_t denominator, numerator; 
                    if (i > j) { 
                        denominator = i - j;
                    } 
                    else { 
                        denominator = Mersenne::neg(j - i);
                    }
                    if (r > j) { 
                        numerator = r - j; 
                    } 
                    else { 
                        numerator = Mersenne::neg(j - r);
                    }
                    result[i] = Mersenne::mul(result[i], Mersenne::mul(Mersenne::inverse(denominator), numerator));
                }
            }
        }
    }

    static void append_one_msg(LocalHash &hash, uint64_t msg) {
        hash.update(msg);
    }

    static void append_msges(LocalHash &hash, vector<uint64_t> msges) {
        for(uint64_t msg: msges) {
            hash.update(msg);
        }
    }
};

#endif