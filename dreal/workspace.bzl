load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl",
    "github_archive",
)
load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/pkg_config.bzl",
    "pkg_config_repository",
)
load(
    "//third_party/com_github_tensorflow_tensorflow/py:python_configure.bzl",
    "python_configure",
)
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@dreal//tools:gmp_repository.bzl", "gmp_repository")

def dreal_workspace():
    pkg_config_repository(
        name = "ibex",  # LGPL3
        modname = "ibex",
        pkg_config_paths = [
            # macOS
            "/usr/local/opt/clp/lib/pkgconfig",
            "/usr/local/opt/coinutils/lib/pkgconfig",
            "/usr/local/opt/ibex@2.7.4/share/pkgconfig",
            "/opt/homebrew/opt/ibex@2.7.4/share/pkgconfig",
            # Linux
            "/usr/lib/pkgconfig",
            "/usr/local/lib/pkgconfig",
            "/opt/libibex/2.7.4/share/pkgconfig",
        ],
    )
    pkg_config_repository(
        name = "nlopt",  # LGPL2 + MIT
        modname = "nlopt",
        pkg_config_paths = [
            "/usr/local/opt/nlopt/lib/pkgconfig",
            "/usr/local/lib64/pkgconfig",
        ],
    )

    gmp_repository(name = "gmp")

    python_configure(name = "local_config_python")

    native.register_toolchains("@local_config_python//:py_toolchain")

    http_archive(
        name = "rules_license",
        sha256 = "26d4021f6898e23b82ef953078389dd49ac2b5618ac564ade4ef87cced147b38",
        urls = [
            "https://github.com/bazelbuild/rules_license/releases/download/1.0.0/rules_license-1.0.0.tar.gz",
        ],
    )

    http_archive(
        name = "rules_pkg",
        sha256 = "d20c951960ed77cb7b341c2a59488534e494d5ad1d30c4818c736d57772a9fef",
        urls = [
            "https://github.com/bazelbuild/rules_pkg/releases/download/1.0.1/rules_pkg-1.0.1.tar.gz",
        ],
    )

    github_archive(
        name = "spdlog",  # MIT
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
        commit = "v1.11.0",
        repository = "gabime/spdlog",
        sha256 = "ca5cae8d6cac15dae0ec63b21d6ad3530070650f68076f3a4a862ca293a858bb",
    )

    github_archive(
        name = "fmt",  # MIT
        build_file = str(Label("//tools:fmt.BUILD.bazel")),
        commit = "9.1.0",
        repository = "fmtlib/fmt",
        sha256 = "5dea48d1fcddc3ec571ce2058e13910a0d4a6bab4cc09a809d8b1dd1c88ae6f2",
    )

    github_archive(
        name = "picosat",  # MIT
        build_file = str(Label("//tools:picosat.BUILD.bazel")),
        commit = "ee542566ca89717af1b4558b0b3f226eb3b6b42d",  # v965 + custom fix
        repository = "dreal-deps/picosat",
        sha256 = "9a047b7ba3ac1075a2288d35045585e2e3c24961f078f30ad97a313b8e539eb2",
    )

    github_archive(
        name = "pybind11",  # BSD
        build_file = str(Label("//tools:pybind11.BUILD.bazel")),
        commit = "v2.10.2",
        repository = "pybind/pybind11",
        sha256 = "93bd1e625e43e03028a3ea7389bba5d3f9f2596abc074b068e70f4ef9b1314ae",
    )

    github_archive(
        name = "com_google_absl",  # BSD
        commit = "20250814.1",
        repository = "abseil/abseil-cpp",
        sha256 = "1692f77d1739bacf3f94337188b78583cf09bab7e420d2dc6c5605a4f86785a1",
    )

    github_archive(
        name = "cds",  # BSL 1.0
        build_file = str(Label("//tools:cds.BUILD.bazel")),
        commit = "v2.3.3",
        repository = "khizmax/libcds",
        sha256 = "f090380ecd6b63a3c2b2f0bdb27260de2ccb22486ef7f47cc1175b70c6e4e388",
    )

    github_archive(
        name = "json",  # MIT
        commit = "b2306145e1789368e6f261680e8dc007e91cc986",  # 20230131
        repository = "nlohmann/json",
        sha256 = "dfb6ec5af1feeb9ce7efa1554676335ca9dde5f60424642c8ac2f9e0a66da909",
    )
