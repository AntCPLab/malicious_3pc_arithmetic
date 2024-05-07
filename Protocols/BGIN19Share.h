#ifndef PROTOCOLS_BGIN19SHARE_H_
#define PROTOCOLS_BGIN19SHARE_H_

#include "Math/FixedVec.h"
#include "Math/Integer.h"
#include "Protocols/Replicated.h"
#include "Protocols/BGIN19Protocol.h"
#include "GC/ShareSecret.h"
#include "ShareInterface.h"
#include "Processor/Instruction.h"

#include "Protocols/Rep3Share.h"
#include "global_debug.hpp"

template<class T>
class BGIN19Share : public RepShare<T, 2>
{
    typedef RepShare<T, 2> super;
    typedef BGIN19Share This;

public:
    typedef T clear;

    typedef BGIN19Protocol<BGIN19Share> Protocol;
    typedef ReplicatedMC<BGIN19Share> MAC_Check;
    typedef MAC_Check Direct_MC;
    typedef ReplicatedInput<BGIN19Share> Input;
    typedef ReplicatedPO<This> PO;
    typedef SpecificPrivateOutput<This> PrivateOutput;
    typedef ReplicatedPrep<BGIN19Share> LivePrep;
    typedef ReplicatedRingPrep<BGIN19Share> TriplePrep;
    typedef BGIN19Share Honest;

    typedef BGIN19Share Scalar;

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

    static BGIN19Share constant(T value, int my_num,
            typename super::mac_key_type = {})
    {
        return BGIN19Share(value, my_num);
    }

    BGIN19Share()
    {
        if (BUILDING_SHARE_PROCESS & SEMI3_RING_SHARE_PROCESS) {
            cout << "In BGIN19Share()" << endl;
        }
    }
    template<class U>
    BGIN19Share(const U& other) :
            super(other)
    {
        if (BUILDING_SHARE_PROCESS & SEMI3_RING_SHARE_PROCESS) {
            cout << "In BGIN19Share(const U& other)" << endl;
        }
    }

    BGIN19Share(T value, int my_num, const T& alphai = {})
    {

        if (BUILDING_SHARE_PROCESS & SEMI3_RING_SHARE_PROCESS) {
            cout << "In BGIN19Share(T value, int my_num, const T& alphai = {})" << endl;
            cout << "assinging " << value << " to " << my_num << endl;
        }

        (void) alphai;

        BGIN19Protocol<BGIN19Share>::assign(*this, value, my_num);
    }

    void assign(const char* buffer)
    {
        if (BUILDING_SHARE_PROCESS & SEMI3_RING_SHARE_PROCESS) {
            cout << "In BGIN19Share::assign(const char* buffer)" << endl;
            cout << "assinging " << buffer << endl;
        }
        FixedVec<T, 2>::assign(buffer);
    }

    clear local_mul(const BGIN19Share& other) const
    {
        auto a = (*this)[0].lazy_mul(other.lazy_sum());
        auto b = (*this)[1].lazy_mul(other[0]);
        return a.lazy_add(b);
    }
};

#endif /* PROTOCOLS_BGIN19Share_H_ */
