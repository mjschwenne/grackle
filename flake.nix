{
  description = "A Flake for Grackle Development";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/a595dde4d0d31606e19dcec73db02279db59d201";
    flake-utils.url = "github:numtide/flake-utils";
    perennial = {
      # The github fecther doesn't support submodules for some reason...
      url = "git+https://github.com/mit-pdos/perennial.git";
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
        perennial-pkg = perennial.packages.${system}.default;
        rocq-build = pkgs.callPackage ./nix/rocq-build {perennial = perennial-pkg;};
      in {
        packages = {
          inherit grackle goose rocq-build;
          default = grackle;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              # Rocq deps
              rocq-core
              rocqPackages.stdlib
              perennial-pkg

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
            ];
            shellHook = ''
              unset COQPATH
            '';
          };
      }
    );
}
