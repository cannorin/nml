MONO_PATH?=/usr/bin

EX_NUGET:=nuget/bin/nuget
PACKAGES:=packages/Mono.Terminal.5.3.0/Mono.Terminal.5.3.0.nupkg

ifeq (, $(shell which msbuild))
XBUILD?=$(MONO_PATH)/xbuild /clp:Verbosity=minimal
else
XBUILD?=$(MONO_PATH)/msbuild /m /v:m
endif

MONO?=$(MONO_PATH)/mono
GIT?=$(shell which git)

NUGET?=$(EX_NUGET)

all: release ;

debug: bin/Debug/nml.Core.dll ;
release: bin/Release/nml.Core.dll ;

bin/Debug/nml.Core.dll: packages
	$(XBUILD) nml.sln

bin/Release/nml.Core.dll: packages
	$(XBUILD) nml.sln /p:Configuration=Release

# NuGet

nuget: $(NUGET) ;

$(EX_NUGET):
	$(GIT) submodule update --init --recursive
	cd nuget && $(MAKE)

packages: nuget $(PACKAGES) ;

$(PACKAGES):
	$(NUGET) restore nml.sln

# Clean

clean:
	$(RM) -r src/core/obj
	$(RM) -r src/interpreter/obj
	$(RM) -r bin/

