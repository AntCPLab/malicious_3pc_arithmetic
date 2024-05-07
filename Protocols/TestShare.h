/*
 * Rep3Share.h
 *
 */

#ifndef PROTOCOLS_TESTSHARE_H_
#define PROTOCOLS_TESTSHARE_H_

#include "Math/FixedVec.h"
#include "Math/Integer.h"
#include "Protocols/Replicated.h"
#include "Protocols/TestProtocol.h"
#include "GC/ShareSecret.h"
#include "ShareInterface.h"
#include "Processor/Instruction.h"

#include "Protocols/Rep3Share.h"
#include "global_debug.hpp"

template<class T>
class TestShare : public RepShare<T, 2>
{
    typedef RepShare<T, 2> super;
    typedef TestShare This;

public:
    typedef T clear;

    typedef TestProtocol<TestShare> Protocol;
    typedef ReplicatedMC<TestShare> MAC_Check;
    typedef MAC_Check Direct_MC;
    typedef ReplicatedInput<TestShare> Input;
    typedef ReplicatedPO<This> PO;
    typedef SpecificPrivateOutput<This> PrivateOutput;
    typedef ReplicatedPrep<TestShare> LivePrep;
    typedef ReplicatedRingPrep<TestShare> TriplePrep;
    typedef TestShare Honest;

    typedef TestShare Scalar;

    typedef GC::SemiHonestRepSecret bit_type;

    const static bool needs_ot = false;
    const static bool dishonest_majority = false;
    const static bool expensive = false;
    const static bool variable_players = false;
    static const bool has_trunc_pr = true;
    static const bool malicious = false;
    bool is_zero_share = false;

    static string type_short()
    {
        return "T3" + string(1, clear::type_char());
    }
    static string type_string()
    {
        return "Test " + T::type_string();
    }
    static char type_char()
    {
        return T::type_char();
    }

    static TestShare constant(T value, int my_num,
            typename super::mac_key_type = {})
    {
        return TestShare(value, my_num);
    }

    TestShare()
    {
        if (BUILDING_SHARE_PROCESS & SEMI3_RING_SHARE_PROCESS) {
            cout << "In TestShare()" << endl;
        }
    }
    template<class U>
    TestShare(const U& other) :
            super(other)
    {
        if (BUILDING_SHARE_PROCESS & SEMI3_RING_SHARE_PROCESS) {
            cout << "In TestShare(const U& other)" << endl;
        }
    }

    TestShare(T value, int my_num, const T& alphai = {})
    {

        if (BUILDING_SHARE_PROCESS & SEMI3_RING_SHARE_PROCESS) {
            cout << "In TestShare(T value, int my_num, const T& alphai = {})" << endl;
            cout << "assinging " << value << " to " << my_num << endl;
        }

        (void) alphai;

        TestProtocol<TestShare>::assign(*this, value, my_num);
    }

    void assign(const char* buffer)
    {
        if (BUILDING_SHARE_PROCESS & SEMI3_RING_SHARE_PROCESS) {
            cout << "In TestShare::assign(const char* buffer)" << endl;
            cout << "assinging " << buffer << endl;
        }
        FixedVec<T, 2>::assign(buffer);
    }

    clear local_mul(const TestShare& other) const
    {
        auto a = (*this)[0].lazy_mul(other.lazy_sum());
        auto b = (*this)[1].lazy_mul(other[0]);
        return a.lazy_add(b);
    }
};

#endif /* PROTOCOLS_TestShare_H_ */
