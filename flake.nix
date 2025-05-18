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
          vendorHash = "sha256-c9+npmcdynfqSnxEZSdubVeN8Y3eYAwjya52vTJayY0=";
          nativeBuildInputs = with pkgs; [protobuf];
        };
        goose = pkgs.buildGoModule {
          name = "goose";
          src = pkgs.fetchFromGitHub {
            owner = "goose-lang";
            repo = "goose";
            rev = "d3a52bb20408699c9eef8cae73a43e4698594663"; # new
            sha256 = "1alkj89nx342qvixfq9r5qiipwb54lb4p8j3chqi64h9i4cc5prb";
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
              # Coq deps
              coq
              coqPackages.stdlib

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
