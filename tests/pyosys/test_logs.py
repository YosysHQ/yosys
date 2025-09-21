from pyosys import libyosys as ys

d = ys.Design(); ys.log_header(d, "foo\n")
ys.log("foo\n")
ys.log_warning("foo\n")
ys.log_warning_noprefix("foo\n")
ys.log_file_info("foo.ys", 1, "foo\n")
ys.log_file_warning("foo.ys", 1, "foo\n")
