{ pkgs, lib, inputs, config, ... }:
let
  cfg = config.hugr;
  darwinRuntimeLibraries = with pkgs; [
    libiconv
    xz
    libffi
    libxml2
    ncurses
  ];
  darwinRuntimeLibraryPath = lib.makeLibraryPath darwinRuntimeLibraries;
in
{
  options.hugr = {
    llvmVersion = lib.mkOption {
      type = lib.types.str;
      default = "21";
    };
  };

  config = {
    # https://devenv.sh/packages/
    # on macos frameworks have to be explicitly specified
    # otherwise a linker error occurs on rust packages
    packages = [
      pkgs.just
      pkgs.graphviz
      pkgs.cargo-insta
      pkgs.cargo-nextest
      pkgs.cargo-dist
      pkgs.capnproto

      # These are required for hugr-llvm to be able to link to llvm.
      pkgs.libffi
      pkgs.libxml2
      pkgs.ncurses
    ] ++ lib.optionals pkgs.stdenv.isDarwin darwinRuntimeLibraries;

    env = let
      llvmPackage = pkgs."llvmPackages_${cfg.llvmVersion}";
      versionInfo = builtins.splitVersion llvmPackage.release_version;
      llvmVersionMajor = builtins.elemAt versionInfo 0;
      llvmVersionMinor = builtins.elemAt versionInfo 1;
    in {
      "LLVM_SYS_${llvmVersionMajor}${llvmVersionMinor}_PREFIX" = "${llvmPackage.libllvm.dev}";
    } // lib.optionalAttrs pkgs.stdenv.isDarwin {
      # `uv` and other prebuilt binaries on macOS can link against `libiconv.2`
      # without carrying an absolute runtime path to the Nix-provided library.
      # Make the fallback loader path explicit so `uv sync` stays stable across
      # devenv/nixpkgs updates instead of depending on incidental shell state.
      DYLD_FALLBACK_LIBRARY_PATH = darwinRuntimeLibraryPath;
    };


    enterShell = ''
      cargo --version
    '';

    languages.python = {
      enable = true;
      uv = {
        enable = true;
#        sync.enable = true;
      };
      venv.enable = true;
    };


    # https://devenv.sh/languages/
    # https://devenv.sh/reference/options/#languagesrustversion
    languages.rust = {
      channel = "stable";
      enable = true;
      components = [ "rustc" "cargo" "clippy" "rustfmt" "rust-analyzer" ];
    };
  };
  # See full reference at https://devenv.sh/reference/options/
}
