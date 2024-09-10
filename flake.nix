{
  description = "A Flake for my Independent Study with Tej Chajed";

  inputs = {
    nixpkgs.url = "nixpkgs";
  };

  outputs = {
    nixpkgs,
    ...
  }: let
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
          rev = "6787e01cef93d900c0018ed84f44141f26d1fbb9";
          hash = "sha256-6HywCVDZF1AVRgsLaIWiuvJcrEr75WOLXXdvgpgF2DU=";
        };
        vendorHash = "sha256-sI5HJmskJ+Qdf7lgbk2ztE4gfRY6YvR7wxK2g3knQko=";
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
