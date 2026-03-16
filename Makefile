# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile doc
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

# Directories for documentation generation
SRC_DIR = src
LATEX_DIR = latex

# Tools
ROQC = rocq
PDFLATEX = pdflatex

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(ROQC) makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# Find all .v files in src directory
V_FILES := $(wildcard $(SRC_DIR)/*.v)
# Get just the filenames without path or extension
V_NAMES := $(notdir $(V_FILES:.v=))
# Generate corresponding .v.tex filenames in latex directory
TEX_FILES := $(addprefix $(LATEX_DIR)/, $(addsuffix .v.tex, $(V_NAMES)))

# Create latex directory if it doesn't exist
$(LATEX_DIR):
	mkdir -p $(LATEX_DIR)

# Pattern rule to generate .v.tex files
# -l 6 skips the first 6 lines (header)
# --body-only ensures only the body content is included
$(LATEX_DIR)/%.v.tex: $(SRC_DIR)/%.v | $(LATEX_DIR)
	@echo "Generating documentation for $< (skipping first 6 lines)..."
	cd $(LATEX_DIR) && $(ROQC) doc --latex --body-only -l -s ../$<
	@# rocq doc generates .tex files, rename them to .v.tex
	cd $(LATEX_DIR) && mv $*.tex $*.v.tex 2>/dev/null || true
	@echo "Generated $@"

# Target to generate all .v.tex files
.PHONY: tex-fragments
tex-fragments: $(TEX_FILES)
	@echo "All documentation files generated in $(LATEX_DIR)/"
	@ls -la $(LATEX_DIR)/*.v.tex 2>/dev/null || echo "No .v.tex files found"

# Debug target to see what rocq doc actually generates
.PHONY: debug-rocq-doc
debug-rocq-doc: | $(LATEX_DIR)
	@echo "Testing rocq doc on first .v file with -l -s option..."
	@cd $(LATEX_DIR) && $(ROQC) doc --latex -l -s ../$(firstword $(V_FILES))
	@echo "Files generated in $(LATEX_DIR):"
	@ls -la $(LATEX_DIR)/*
	@echo ""
	@echo "First 10 lines of generated .tex file (should start at line 7 of original):"
	@head -10 $(LATEX_DIR)/$(firstword $(V_NAMES)).tex 2>/dev/null || echo "No .tex file found"

# Individual file target (kept for backward compatibility)
.PHONY: tex-fragment-%
tex-fragment-%: $(LATEX_DIR)/%.v.tex
	@echo "Generated $<"

# Main documentation target - THIS IS THE IMPORTANT PART
# Make it a phony target so it's always considered out of date
.PHONY: doc
doc: $(LATEX_DIR)/relatorio.pdf
	@echo "Documentation generated successfully"

$(LATEX_DIR)/relatorio.pdf: $(LATEX_DIR)/relatorio.tex $(TEX_FILES) | $(LATEX_DIR)
	cd $(LATEX_DIR) && $(PDFLATEX) relatorio
	cd $(LATEX_DIR) && $(PDFLATEX) relatorio
	cd $(LATEX_DIR) && $(PDFLATEX) relatorio

# Clean documentation files
.PHONY: clean-doc
clean-doc:
	rm -rf $(LATEX_DIR)/*.aux $(LATEX_DIR)/*.log $(LATEX_DIR)/*.out
	rm -f $(LATEX_DIR)/*.v.tex 

# Add doc cleaning to the main clean target
.PHONY: clean
clean: clean-doc
	$(MAKE) --no-print-directory -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf

# Show debug information
.PHONY: debug-doc
debug-doc:
	@echo "SRC_DIR = $(SRC_DIR)"
	@echo "LATEX_DIR = $(LATEX_DIR)"
	@echo "V_FILES = $(V_FILES)"
	@echo "V_NAMES = $(V_NAMES)"
	@echo "TEX_FILES = $(TEX_FILES)"
	@echo "ROQC = $(ROQC)"
	@echo "PDFLATEX = $(PDFLATEX)"
	@echo ""
	@echo "Files in $(SRC_DIR):"
	@ls -la $(SRC_DIR)/*.v 2>/dev/null || echo "No .v files found"

# Open pdf with evince
.PHONY: pdf
pdf:
	evince $(LATEX_DIR)/relatorio.pdf&

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
