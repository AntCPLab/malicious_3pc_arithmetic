
#include "Protocols/TestShare.h"
#include "Protocols/TestRingShare.h"
#include "Protocols/TestProtocol.hpp"
#include "Protocols/ReplicatedPrep.hpp"
#include "Machines/Rep.hpp"
#include "Protocols/Replicated.hpp"

#include "Math/Integer.h"
#include "Processor/RingMachine.hpp"

int main(int argc, const char **argv) {

    HonestMajorityRingMachine<TestRingShare, TestShare>(argc, argv);
}