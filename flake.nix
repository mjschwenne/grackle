{
  description = "A Flake for my Independent Study with Tej Chajed";

  inputs = {
    nixpkgs.url = "nixpkgs";
  };

  outputs = {nixpkgs, ...}: let
    system = "x86_64-linux";
  in {
    devShells."${system}".default = let
      pkgs = import nixpkgs {
        inherit system;
      };
      goose = pkgs.buildGoModule {
        name = "goose";
        src = pkgs.fetchFromGitHub {
          owner = "goose-lang";
          repo = "goose";
          rev = "a4f2f84193d34f56dd84fc623adc43a6441da1eb";
          sha256 = "1b1dfa1qsv2h7hy5x20zhic2npr5gz1zp76m1lab4v490adxj2rx";
        };
        vendorHash = "sha256-HCJ8v3TSv4UrkOsRuENWVz5Z7zQ1UsOygx0Mo7MELzY=";
      };
    in
      pkgs.mkShell {
        # create an environment with the required coq libraries
        packages = with pkgs; [
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
          pkgs.update-nix-fetchgit
          pkgs.nix-prefetch-git
          pkgs.nix-prefetch
        ];

        shellHook = ''
          unset COQPATH
        '';
      };
  };
}
