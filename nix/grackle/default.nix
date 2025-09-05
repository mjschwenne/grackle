{
  buildGoModule,
  protobuf,
  ...
}:
buildGoModule {
  pname = "grackle";
  version = "new";
  src = ../../.;
  vendorHash = "sha256-9SPrti4GPjY078yi2xok7eW/XRntChdmowaJ1xTdE8M=";
  nativeBuildInputs = [protobuf];
}
