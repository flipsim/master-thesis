all: build clean

build:
	rocq makefile -f _CoqProject -o CoqMakefile
	make -f CoqMakefile

clean:
	@find . -name "*.aux" -type f -delete
	@find . -name "*.vok" -type f -delete
	@find . -name "*.vos" -type f -delete
	@find . -name "*.glob" -type f -delete
	@echo "Cleanup complete."