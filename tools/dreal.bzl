# Based on Drake's drake.bzl file,
# https://github.com/RobotLocomotion/drake/blob/master/tools/drake.bzl.

load("@rules_python//python:defs.bzl", "py_library", "py_test")

DREAL_VERSION = "4.21.06.2"

DREAL_PREFIX = "opt/dreal/%s" % DREAL_VERSION

PYTHON_VERSION_STRING = "3"

PYTHON_PACKAGE_DIR = "lib/python" + PYTHON_VERSION_STRING + "/site-packages"

# The CXX_FLAGS will be enabled for all C++ rules in the project
# building with any compiler.
CXX_FLAGS = [
    "-Wall",
    "-Wattributes",
    "-Wdeprecated",
    "-Wdeprecated-declarations",
    "-Wextra",
    "-Wignored-qualifiers",
    "-Wold-style-cast",
    "-Woverloaded-virtual",
    "-Wpedantic",
    "-Wshadow",
]

# The CLANG_FLAGS will be enabled for all C++ rules in the project when
# building with clang.
CLANG_FLAGS = CXX_FLAGS + [
    "-Wabsolute-value",
    "-Winconsistent-missing-override",
    "-Wnon-virtual-dtor",
    "-Wreturn-stack-address",
    "-Wsign-compare",
]

# The GCC_FLAGS will be enabled for all C++ rules in the project when
# building with gcc.
GCC_FLAGS = CXX_FLAGS + [
    "-Wlogical-op",
    "-Wnon-virtual-dtor",
    "-Wreturn-local-addr",
    "-Wunused-but-set-parameter",
]

# The GCC_CC_TEST_FLAGS will be enabled for all cc_test rules in the project
# when building with gcc.
GCC_CC_TEST_FLAGS = [
    "-Wno-unused-parameter",
]

def _platform_copts(rule_copts, cc_test = 0):
    """Returns both the rule_copts, and platform-specific copts.

    When cc_test=1, the GCC_CC_TEST_FLAGS will be added.  It should only be set
    to 1 from cc_test rules or rules that are boil down to cc_test rules.
    """
    extra_gcc_flags = []
    if cc_test:
        extra_gcc_flags = GCC_CC_TEST_FLAGS
    return select({
        "//tools:gcc_build": GCC_FLAGS + extra_gcc_flags + rule_copts,
        "//tools:clang_build": CLANG_FLAGS + rule_copts,
        "//conditions:default": CXX_FLAGS + rule_copts,
    })

def _check_library_deps_blacklist(name, deps):
    """Report an error if a library should not use something from deps."""
    if not deps:
        return
    if type(deps) != "list":
        # We can't handle select() yet.
        return
    for dep in deps:
        if dep.endswith(":main"):
            fail("The cc_library '" + name + "' must not depend on a :main " +
                 "function from a cc_library; only cc_binary program should " +
                 "have a main function")

def _check_pybind_cc_deps(name, cc_deps, testonly = False):
    """Fails-fast in case of potential ODR violations in pybind libraries.

    Pybind libraries link against the shared library, so any cc_deps that
    are also linked into the shared library would cause ODR violations.
    Only header-only libraries should be allowed as cc_deps.
    """
    if not cc_deps:
        return
    if type(cc_deps) != "list":
        return

    # Allowed prefixes for cc_deps (header-only or pybind-specific)
    allowed_prefixes = [
        # Local pybind targets
        ":",
        # dreal utility headers that are header-only
        "//dreal/util:fmt",
    ]

    if testonly:
        # Test utilities are not part of libdreal.so
        allowed_prefixes.append("//dreal/test")

    for dep in cc_deps:
        is_allowed = False
        for prefix in allowed_prefixes:
            if dep.startswith(prefix):
                is_allowed = True
                break
        if not is_allowed:
            fail(("The pybind library '{}' has cc_dep '{}' which may cause " +
                  "ODR violations. Only header-only libraries should be in " +
                  "cc_deps. Other dependencies should come through the " +
                  "shared library.").format(name, dep))

def get_pybind_package_info(base_package = "//dreal"):
    """Returns a struct with Python package path information.

    This provides consistent PYTHONPATH configuration and installation paths
    for pybind libraries.

    Args:
        base_package: The base package for Python bindings (default "//dreal")

    Returns:
        A struct with:
            py_imports: List of import paths for PYTHONPATH
            py_dest: Installation destination for Python files
            base_package: The base package path
    """
    # Calculate the relative path from the current package to the base
    return struct(
        py_imports = ["."],
        py_dest = PYTHON_PACKAGE_DIR,
        base_package = base_package,
    )

def dreal_cc_library(
        name,
        hdrs = None,
        srcs = None,
        deps = None,
        copts = [],
        linkstatic = 1,
        alwayslink = 1,
        **kwargs):
    """Creates a rule to declare a C++ library.
    """
    _check_library_deps_blacklist(name, deps)
    native.cc_library(
        name = name,
        hdrs = hdrs,
        srcs = srcs,
        deps = deps,
        linkstatic = linkstatic,
        alwayslink = alwayslink,
        copts = _platform_copts(copts),
        **kwargs
    )

def _make_search_paths(prefix, levels_to_root):
    return ",".join(
        [
            "-rpath,%s/%s" % (prefix, "/".join([".."] * search_level))
            for search_level in range(levels_to_root + 1)
        ],
    )

def dreal_pybind_library(
        name,
        py_srcs = [],
        py_deps = [],
        py_imports = [],
        cc_srcs = [],
        cc_deps = [],
        package_info = None,
        testonly = False,
        visibility = None):
    """Creates a rule to declare a pybind library.

    Args:
        name: The name of the library.
        py_srcs: Python source files.
        py_deps: Python dependencies.
        py_imports: Additional Python import paths.
        cc_srcs: C++ source files for the pybind module.
        cc_deps: C++ dependencies. These should be header-only libraries
            to avoid ODR violations with the shared library.
        package_info: Optional result of get_pybind_package_info() for
            consistent path configuration.
        testonly: If True, relaxes ODR checks for test utilities.
        visibility: Visibility specification.
    """
    # Check for potential ODR violations
    _check_pybind_cc_deps(name, cc_deps, testonly)

    cc_so_name = "_" + name + ".so"

    # The last +3 is for "lib/python*/site-packages".
    levels_to_root = native.package_name().count("/") + name.count("/") + 3

    # Determine imports from package_info or use defaults
    all_py_imports = py_imports
    if package_info:
        all_py_imports = package_info.py_imports + py_imports

    # Default visibility
    if visibility == None:
        visibility = ["//dreal:__subpackages__"]

    dreal_cc_binary(
        name = cc_so_name,
        srcs = cc_srcs,
        copts = [
            "-fexceptions",
            "-fvisibility=hidden",
        ],
        features = [
            "-use_header_modules",
            "-parse_headers",
        ],
        linkopts = select({
            "@dreal//tools:linux": [
                "-Wl,%s" % (_make_search_paths("$$ORIGIN", levels_to_root),),
            ],
            "@dreal//tools:apple": [
                "-undefined",
                "dynamic_lookup",
            ],
            "@//conditions:default": [],
        }),
        linkshared = 1,
        testonly = testonly,
        deps = cc_deps + [
            "//:dreal_shared_library",
            "@pybind11",
        ],
    )
    py_library(
        name = name,
        srcs = py_srcs,
        data = [
            cc_so_name,
        ],
        srcs_version = "PY3",
        imports = all_py_imports,
        visibility = visibility,
        testonly = testonly,
        deps = py_deps,
    )

def dreal_cc_binary(
        name,
        srcs = None,
        deps = None,
        copts = [],
        testonly = 0,
        add_test_rule = 0,
        test_rule_args = [],
        test_rule_size = None,
        **kwargs):
    """Creates a rule to declare a C++ binary.

    If you wish to create a smoke-test demonstrating that your binary runs
    without crashing, supply add_test_rule=1. Note that if you wish to do
    this, you should consider suppressing that urge, and instead writing real
    tests. The smoke-test will be named <name>_test. You may override cc_test
    defaults using test_rule_args=["-f", "--bar=42"] or test_rule_size="baz".
    """
    native.cc_binary(
        name = name,
        srcs = srcs,
        deps = deps,
        copts = _platform_copts(copts),
        testonly = testonly,
        **kwargs
    )

    if add_test_rule:
        dreal_cc_test(
            name = name + "_test",
            srcs = srcs,
            deps = deps,
            copts = copts,
            size = test_rule_size,
            testonly = testonly,
            args = test_rule_args,
            **kwargs
        )

def dreal_cc_test(
        name,
        size = None,
        srcs = None,
        copts = [],
        **kwargs):
    """Creates a rule to declare a C++ unit test.

    Note that for almost all cases, dreal_cc_googletest should be
    used, instead of this rule.

    By default, sets size="small" because that indicates a unit test.
    By default, sets name="test/${name}.cc" per Dreal's filename
    convention.

    """
    if size == None:
        size = "small"
    if srcs == None:
        srcs = ["test/%s.cc" % name]
    native.cc_test(
        name = name,
        size = size,
        srcs = srcs,
        copts = _platform_copts(copts, cc_test = 1),
        **kwargs
    )

def dreal_py_test(
        name,
        srcs,
        main,
        tags,
        deps,
        **kwargs):
    """Creates a rule to declare a Python unit test."""
    py_test(
        name = name,
        srcs = srcs,
        main = main,
        tags = tags,
        deps = deps,
        srcs_version = "PY3",
        **kwargs
    )

def dreal_cc_googletest(
        name,
        deps = None,
        use_default_main = True,
        **kwargs):
    """Creates a rule to declare a C++ unit test using googletest.

    Always adds a deps= entry for googletest main
    (@com_google_googletest//:gtest_main).

    By default, sets size="small" because that indicates a unit test.
    By default, sets name="test/${name}.cc" per Dreal's filename convention.
    By default, sets use_default_main=True to use GTest's main, via
    @com_google_googletest//:gtest_main. Otherwise, it will depend on
    @com_google_googlegtest//:gtest.

    """
    if deps == None:
        deps = []
    if use_default_main:
        deps.append("@com_google_googletest//:gtest_main")
    else:
        deps.append("@com_google_googletest//:gtest")
    dreal_cc_test(
        name = name,
        deps = deps,
        **kwargs
    )

def smt2_test(
        name,
        smt2 = None,
        options = [],
        tags = [],
        **kwargs):
    """Create smt2 test."""
    if not smt2:
        smt2 = name + ".smt2"
    expected = smt2 + ".expected"
    data_files = native.glob([
        smt2 + "*",
    ])
    py_test(
        name = name,
        args = [
            "$(location //dreal:dreal)",
            "$(location %s)" % smt2,
            "$(location %s)" % expected,
        ] + options,
        tags = tags + ["smt2"],
        srcs = ["test.py"],
        data = [
            "//dreal:dreal",
        ] + data_files,
        main = "test.py",
        srcs_version = "PY3",
        **kwargs
    )

def dr_test(
        name,
        args = [],
        **kwargs):
    """Create dr test."""
    dr = name + ".dr"
    expected = dr + ".expected"
    data_files = native.glob([
        dr + "*",
    ])
    py_test(
        name = name,
        args = [
            "$(location //dreal:dreal)",
            "$(location %s)" % dr,
            "$(location %s)" % expected,
        ] + args,
        tags = ["dr"],
        srcs = ["test.py"],
        data = [
            "//dreal:dreal",
        ] + data_files,
        main = "test.py",
        srcs_version = "PY3",
        **kwargs
    )

# Generate a file with specified content
def _generate_file_impl(ctx):
    ctx.actions.write(content = ctx.attr.content, output = ctx.outputs.out)

dreal_generate_file = rule(
    attrs = {
        "content": attr.string(),
        "out": attr.output(mandatory = True),
    },
    output_to_genfiles = True,
    implementation = _generate_file_impl,
)
