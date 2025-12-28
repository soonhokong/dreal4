/// @file fmt.h
/// @brief Centralized fmt::formatter specializations for dReal types.
///
/// Include this header in .cc files that need to format dReal types with
/// spdlog/fmt. This avoids duplicating formatter definitions across files.
#pragma once

#include <fmt/format.h>
#include <fmt/ostream.h>

#include "dreal/smt2/logic.h"
#include "dreal/util/dynamic_bitset.h"

// Forward declarations for types that don't need full definitions
namespace dreal {
class Box;
class Contractor;
class Config;
class FormulaEvaluator;
namespace drake::symbolic {
class Expression;
class Formula;
class Variable;
class Variables;
}  // namespace drake::symbolic
}  // namespace dreal

namespace ibex {
class Interval;
class NumConstraint;
}  // namespace ibex

// All dReal types use ostream_formatter since they have operator<<
template <>
struct fmt::formatter<dreal::Box> : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::Contractor> : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::Config> : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::DynamicBitset> : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::FormulaEvaluator> : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::Logic> : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::drake::symbolic::Expression>
    : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::drake::symbolic::Formula>
    : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::drake::symbolic::Variable>
    : fmt::ostream_formatter {};
template <>
struct fmt::formatter<dreal::drake::symbolic::Variables>
    : fmt::ostream_formatter {};

// IBEX types
template <>
struct fmt::formatter<ibex::Interval> : fmt::ostream_formatter {};
template <>
struct fmt::formatter<ibex::NumConstraint> : fmt::ostream_formatter {};
