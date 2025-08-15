{
  description = "A Flake for Grackle Development";

  inputs = {
    nixpkgs.url = "nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    nixpkgs,
    flake-utils,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        grackle = pkgs.buildGoModule {
          name = "grackle";
          src = ./.;
          vendorHash = "sha256-HByv0JVhqfAGtfnhkoF3tqAW4YGw9O1IM41qc5JEnr0=";
          nativeBuildInputs = with pkgs; [protobuf];
        };
        goose = pkgs.buildGoModule {
          name = "goose";
          src = pkgs.fetchFromGitHub {
            owner = "goose-lang";
            repo = "goose";
            rev = "c14e8e8258e228f43f9e7525d127246e07496523";
            hash = "sha256-FpgY75/ngEqpitCGGxEqCJKJ5NMpZ0+bV+XeA7UVmVo=";
          };
          proxyVendor = true;
          vendorHash = "sha256-MHo+sm5MUP5NVn128vu02zVcs2gpg24zC8o+UvBOnpI=";
        };
      in {
        packages = {
          inherit grackle goose;
          default = grackle;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              # Rocq deps
              rocq-core
              rocqPackages.stdlib

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
              # Should be able to update goose and grackle with `update-nix-fetchgit flake.nix`
              update-nix-fetchgit
              nix-prefetch-git
              nix-prefetch
            ];
            shellHook = ''
              unset COQPATH
            '';
          };
      }
    );
}
