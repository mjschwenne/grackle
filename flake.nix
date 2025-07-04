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
            rev = "2249e1811cc6b39bc3dc03604ec915ab532e391c"; # new
            sha256 = "0rib03751rad8x8n1jcq925yw2ccfhns426f8mfnzq8hsq9mbn08";
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
