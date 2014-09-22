
TARGETS += proc_01 proc_02 proc_03
TARGETS += opt_01 opt_02 opt_03 opt_04
TARGETS += memory_01 memory_02
TARGETS += techmap_01
TARGETS += abc_01

all: $(addsuffix .pdf,$(TARGETS))

define make_pdf_template
$(1).pdf: $(1)*.v $(1)*.ys
	../../yosys -p 'script $(1).ys; show -notitle -prefix $(1) -format pdf'
endef

$(foreach trg,$(TARGETS),$(eval $(call make_pdf_template,$(trg))))

clean:
	rm -f $(addsuffix .pdf,$(TARGETS))
	rm -f $(addsuffix .dot,$(TARGETS))

