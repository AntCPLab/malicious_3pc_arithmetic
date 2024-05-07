
#include "Protocols/BGIN19Share.h"
#include "Protocols/BGIN19RingShare.h"
#include "Protocols/BGIN19Protocol.hpp"
#include "Protocols/ReplicatedPrep.hpp"
#include "Machines/Rep.hpp"
#include "Protocols/Replicated.hpp"

#include "Math/Integer.h"
#include "Processor/RingMachine.hpp"
#include "Tools/performance.h"

int main(int argc, const char **argv) {

    HonestMajorityRingMachine<BGIN19RingShare, BGIN19Share>(argc, argv);
    print_profiling();
}