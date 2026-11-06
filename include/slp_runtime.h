#ifndef ARMOR_SLP_RUNTIME_H_
#define ARMOR_SLP_RUNTIME_H_

#include <cstdint>
#include <x86intrin.h>

namespace armor_slp {

constexpr uint64_t low_mask(unsigned width) {
  return width == 0 ? UINT64_C(0)
                    : (width >= 64 ? UINT64_MAX
                                   : ((UINT64_C(1) << width) - UINT64_C(1)));
}

inline uint64_t unpack_bits(
    uint64_t packed,
    unsigned offset,
    unsigned width) {
  return (packed >> offset) & low_mask(width);
}

inline void pack_bits(
    uint64_t& packed,
    uint64_t value,
    unsigned offset,
    unsigned width) {
  packed |= (value & low_mask(width)) << offset;
}

inline uint64_t replicate_lane_mask(
    unsigned lane_width,
    unsigned lane_count) {
  uint64_t result = 0;
  for (unsigned lane = 0; lane < lane_count; ++lane) {
    pack_bits(result, low_mask(lane_width), lane * lane_width, lane_width);
  }
  return result;
}

}  // namespace armor_slp

#endif  // ARMOR_SLP_RUNTIME_H_
