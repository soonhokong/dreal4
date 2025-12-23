/// @file box_fmt.h
/// Provides fmt formatter for Box.
#pragma once

#include <fmt/format.h>
#include <fmt/ostream.h>

#include "dreal/util/box.h"

template <>
struct fmt::formatter<dreal::Box> : fmt::ostream_formatter {};
