package(default_visibility = ["//visibility:public"])

cc_library(
    name = "ibex",
    srcs = %{srcs},
    hdrs = %{hdrs},
    copts = %{copts},
    defines = %{defines},
    includes = %{includes},
    linkopts = %{linkopts},
    deps = %{deps},
)
