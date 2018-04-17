MONO_PATH?=/usr/bin

DOTNET?=$(shell which dotnet)

all: release

release: bin/Release/netcoreapp2.0/current-platform/nmli.dll

bin/Release/netcoreapp2.0/current-platform/nmli.dll:
	$(DOTNET) publish -c Release -o ../../bin/Release/netcoreapp2.0/current-platform/

run: release
	$(DOTNET) bin/Release/netcoreapp2.0/current-platform/nmli.dll


self-contained-win:
	$(DOTNET) publish -c Release --self-contained --runtime win-x64

self-contained-linux:
	$(DOTNET) publish -c Release --self-contained --runtime linux-x64

self-contained-osx:
	$(DOTNET) publish -c Release --self-contained --runtime osx-x64


debug: bin/Debug/netcoreapp2.0/nmli.dll

bin/Debug/netcoreapp2.0/nmli.dll:
	$(DOTNET) build -c Debug

run-debug: debug
	$(DOTNET) ./bin/Debug/netcoreapp2.0/nmli.dll

# Clean

clean:
	$(RM) -r src/core/obj
	$(RM) -r src/interpreter/obj
	$(RM) -r bin/

