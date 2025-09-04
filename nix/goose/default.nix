{
  buildGoModule,
  fetchFromGitHub,
}: let
  pname = "goose";
  version = "0.9.2-unstable-2025-09-03";
  src = fetchFromGitHub {
    owner = "goose-lang";
    repo = "goose";
    rev = "da51f4aebe46ab4099e1d175bea738dda1614c07";
    hash = "sha256-j04SzgF32CKvbe8WloY/Mdciz68s7yJMcOtdDXvujoY=";
  };
in
  buildGoModule {
    inherit pname version src;
    proxyVendor = true;
    vendorHash = "sha256-MHo+sm5MUP5NVn128vu02zVcs2gpg24zC8o+UvBOnpI=";
  }
