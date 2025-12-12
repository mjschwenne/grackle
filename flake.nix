{
  description = "A Flake for Grackle Development";

  inputs = {
    nixpkgs.url = "github:/NixOS/nixpkgs/f61125a668a320878494449750330ca58b78c557";
    flake-utils.url = "github:numtide/flake-utils";
    perennial = {
      url = "github:mit-pdos/perennial";
      # Break circular dependency, since perennial uses grackle in CI
      inputs.grackle.follows = "/";
    };
  };

  outputs = {
    nixpkgs,
    flake-utils,
    perennial,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        grackle = pkgs.callPackage ./nix/grackle {};
        goose = pkgs.callPackage ./nix/goose {};
        inherit (perennial.packages.${system}) perennialPkgs;
        perennial-pkg = perennial.packages.${system}.default;
        rocq-build = pkgs.callPackage ./nix/rocq-build {
          inherit perennialPkgs;
          perennial = perennial-pkg;
        };
      in {
        packages = {
          inherit grackle goose rocq-build;
          default = grackle;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs =
              [
                # Go deps
                go
                gopls
                goose

                # Protobuf deps
                protobuf
                protoc-gen-go
                proto-contrib
                protoscope

                # nix helpers
                nix-update
              ]
              ++ (with perennialPkgs; [
                rocq-runtime
                rocq-stdlib
                coq-coqutil
                coq-record-update
                rocq-stdpp
                rocq-iris
                iris-named-props
                perennial-pkg
              ]);
            shellHook = ''
              export ROCQPATH=$COQPATH
              unset COQPATH
            '';
          };
      }
    );
}
