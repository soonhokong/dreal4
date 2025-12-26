workspace(name = "dreal")

load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl",
    "github_archive",
)
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

# Override local_config_python before any other loads to avoid Python 2 issues
load("//tools:local_config_python.bzl", "local_config_python")
local_config_python(name = "local_config_python")

github_archive(
    name = "bazel_skylib",  # Apache-2.0
    commit = "1.9.0",
    repository = "bazelbuild/bazel-skylib",
    sha256 = "d9b87903b95e412d37d41a2fa6b0b44b8ba52122c3880512674b26facfc985a2",
)

load("@bazel_skylib//lib:versions.bzl", "versions")

versions.check(minimum_bazel_version = "4.2.1")

github_archive(
    name = "google_styleguide",  # BSD-3
    build_file = "//tools:google_styleguide.BUILD.bazel",
    commit = "2.0.2",
    repository = "cpplint/cpplint",
    sha256 = "fc6d0cd40f934b58e8e0bb5eb5f1f2b651880b5fbc0e93a54e6fb6503f733b3d",
)

github_archive(
    name = "pycodestyle",  # Expat
    build_file = "//tools:pycodestyle.BUILD.bazel",
    commit = "2.14.0",
    repository = "PyCQA/pycodestyle",
    sha256 = "ffcf4dc55f1e5fbdc6dd6acf5db0fd07ded534ae376eee23a742e1410b48d9ae",
)

github_archive(
    name = "ezoptionparser",  # MIT
    build_file = "//tools:ezoptionparser.BUILD.bazel",
    commit = "5bb9214fc26bf14cea071411216e23799cabd0da",
    repository = "dreal-deps/ezoptionparser",
    sha256 = "7349f3091bd05a675a61b61350536f32da77578d3bfb629e2ed5bc31b7a4fa2c",
)

github_archive(
    name = "com_google_googletest",  # GOOGLE
    commit = "v1.17.0",
    repository = "google/googletest",
    sha256 = "65fab701d9829d38cb77c14acdc431d2108bfdbf8979e40eb8ae567edf10b27c",
)

# Note: Dependency of rules_pkg in dreal/workspace.bzl
http_archive(
    name = "rules_python",  # Apache-2.0
    sha256 = "f609f341d6e9090b981b3f45324d05a819fd7a5a56434f849c761971ce2c47da",
    strip_prefix = "rules_python-1.7.0",
    url = "https://github.com/bazelbuild/rules_python/releases/download/1.7.0/rules_python-1.7.0.tar.gz",
)

load("@rules_python//python:repositories.bzl", "py_repositories")

py_repositories()

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
