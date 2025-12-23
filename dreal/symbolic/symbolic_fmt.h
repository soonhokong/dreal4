/// @file symbolic_fmt.h
/// Provides fmt formatters for symbolic types.
#pragma once

#include <fmt/format.h>
#include <fmt/ostream.h>

#include "dreal/symbolic/symbolic.h"

template <>
struct fmt::formatter<dreal::drake::symbolic::Formula>
    : fmt::ostream_formatter {};

template <>
struct fmt::formatter<dreal::drake::symbolic::Expression>
    : fmt::ostream_formatter {};

template <>
struct fmt::formatter<dreal::drake::symbolic::Variable>
    : fmt::ostream_formatter {};

template <>
struct fmt::formatter<dreal::drake::symbolic::Variable::Type>
    : fmt::ostream_formatter {};

template <>
struct fmt::formatter<dreal::drake::symbolic::Variables>
    : fmt::ostream_formatter {};

template <>
struct fmt::formatter<dreal::drake::symbolic::Environment>
    : fmt::ostream_formatter {};
