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
            "/opt/libibex/2.7.4/share/pkgconfig",
        ],
    )
    pkg_config_repository(
        name = "nlopt",  # LGPL2 + MIT
        modname = "nlopt",
        pkg_config_paths = [
            "/usr/local/opt/nlopt/lib/pkgconfig",
        ],
    )

    gmp_repository(name = "gmp")

    # Note: local_config_python is now defined in WORKSPACE to support Bazel 8
    # python_configure(name = "local_config_python")

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
        sha256 = "b5c9184a23bb0bcff241981fd9d9e2a97638a1374c9953bb1808836ce711f990",
        urls = [
            "https://github.com/bazelbuild/rules_pkg/releases/download/1.2.0/rules_pkg-1.2.0.tar.gz",
        ],
    )

    github_archive(
        name = "spdlog",  # MIT
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
        commit = "v1.16.0",
        repository = "gabime/spdlog",
        sha256 = "8741753e488a78dd0d0024c980e1fb5b5c85888447e309d9cb9d949bdb52aa3e",
    )

    github_archive(
        name = "fmt",  # MIT
        build_file = str(Label("//tools:fmt.BUILD.bazel")),
        commit = "12.0.0",
        repository = "fmtlib/fmt",
        sha256 = "aa3e8fbb6a0066c03454434add1f1fc23299e85758ceec0d7d2d974431481e40",
    )

    github_archive(
        name = "picosat",  # MIT
        build_file = str(Label("//tools:picosat.BUILD.bazel")),
        commit = "7670e793684592564d3992dbcb3dcae20f2bd95d",
        repository = "dreal-deps/picosat",
        sha256 = "33e197f810f6b53fac88608bcfffdebe96e8bb01700e17933aa54a004c37827f",
    )

    github_archive(
        name = "pybind11",  # BSD
        build_file = str(Label("//tools:pybind11.BUILD.bazel")),
        commit = "v3.0.1",
        repository = "pybind/pybind11",
        sha256 = "741633da746b7c738bb71f1854f957b9da660bcd2dce68d71949037f0969d0ca",
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
        build_file = str(Label("//tools:json.BUILD.bazel")),
        commit = "v3.12.0",
        repository = "nlohmann/json",
        sha256 = "4b92eb0c06d10683f7447ce9406cb97cd4b453be18d7279320f7b2f025c10187",
    )
