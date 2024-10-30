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
          rev = "585abc3cfef50dd466e112d7c535dbdfccd3c0ca";
          hash = "sha256-M4zaZ1DdecYXeDugrL+TV7HWPMLuj1P25G6mf+fgljg=";
        };
        vendorHash = "sha256-HCJ8v3TSv4UrkOsRuENWVz5Z7zQ1UsOygx0Mo7MELzY=";
      };
    in
      pkgs.mkShell {
        # create an environment with the required coq libraries
        packages = with pkgs; [
          # Coq deps
          coq

          # Go deps
          go
          gopls
          goose

          # Protobuf deps
          protobuf
          protoc-gen-go
          proto-contrib
          protoscope
        ];

        shellHook = ''
        '';
      };
  };
}
