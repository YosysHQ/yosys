var YosysJS = new function() {
	this.script_element = document.currentScript;
	this.viz_element = undefined;
	this.viz_ready = true;

	this.url_prefix = this.script_element.src.replace(/[^/]+$/, '')

	this.load_viz = function() {
		if (this.viz_element)
			return;

		this.viz_element = document.createElement('iframe')
		this.viz_element.style.display = 'none'
		document.body.appendChild(this.viz_element);

		this.viz_element.contentWindow.document.open();
		this.viz_element.contentWindow.document.write('<script type="text/javascript" onload="viz_ready = true;" src="' + this.url_prefix + 'viz.js"></' + 'script>');
		this.viz_element.contentWindow.document.close();

		var that = this;
		function check_viz_ready() {
			if (that.viz_element.contentWindow.viz_ready) {
				console.log("YosysJS: Successfully loaded Viz.");
				that.viz_ready = true;
			} else
				window.setTimeout(check_viz_ready, 100);
		}

		this.viz_ready = false;
		window.setTimeout(check_viz_ready, 100);
	}

	this.dot_to_svg = function(dot_text) {
		return this.viz_element.contentWindow.Viz(dot_text, "svg");
	}

	this.dot_into_svg = function(dot_text, svg_element) {
		if (typeof(svg_element) == 'string' && svg_element != "")
			svg_element = document.getElementById(svg_element);
		svg_element.innerHTML = this.dot_to_svg(dot_text);
		c = svg_element.firstChild;
		while (c) {
			if (c.tagName == 'svg') {
				while (c.firstChild)
					svg_element.appendChild(c.firstChild);
				svg_element.setAttribute('viewBox', c.getAttribute('viewBox'));
				// svg_element.removeChild(c);
				break;
			}
			c = c.nextSibling;
		}
	}

	this.create = function(reference_element, on_ready) {
		var ys = new Object();
		ys.YosysJS = this;
		ys.init_script = "";
		ys.ready = false;
		ys.verbose = false;
		ys.logprint = false;
		ys.echo = false;
		ys.errmsg = "";

		if (typeof(reference_element) == 'string' && reference_element != "")
			reference_element = document.getElementById(reference_element);

		if (reference_element) {
			if (reference_element.tagName == 'textarea')
				ys.init_script = reference_element.value;

			if (reference_element.tagName == 'iframe') {
				ys.iframe_element = reference_element;
			} else {
				ys.iframe_element = document.createElement('iframe');
				ys.iframe_element.id = reference_element.id;
				for (i in reference_element.style)
					ys.iframe_element.style[i] = reference_element.style[i];
				reference_element.parentNode.insertBefore(ys.iframe_element, reference_element);
				reference_element.parentNode.removeChild(reference_element);
			}
		} else {
			ys.iframe_element = document.createElement('iframe');
			ys.iframe_element.style.display = 'none';
			document.body.appendChild(ys.iframe_element);
		}

		ys.print_buffer = "";
		ys.last_line_empty = false;
		ys.got_normal_log_message = false;
		ys.window = ys.iframe_element.contentWindow;

		var doc = ys.window.document;
		var mod = ys.window.Module = {
			print: function(text) {
				if (typeof(text) == 'number')
					return;
				ys.print_buffer += text + "\n";
				ys.got_normal_log_message = true;
				if (ys.logprint)
					console.log(text);
				if (ys.verbose) {
					ys.last_line_empty = text == "";
					if (text == "") {
						span = doc.createElement('br');
					} else {
						span = doc.createElement('span');
						span.textContent = text + "\n";
						span.style.fontFamily = 'monospace';
						span.style.whiteSpace = 'pre';
					}
					doc.firstChild.appendChild(span);
					if (doc.body)
						ys.window.scrollTo(0, doc.body.scrollHeight);
					else
						ys.window.scrollBy(0, 100);
				}
				ys.ready = true;
			},
			printErr: function(text) {
				if (typeof(text) == 'number')
					return;
				if (ys.logprint)
					console.log(text);
				if (ys.got_normal_log_message) {
					ys.print_buffer += text + "\n";
					ys.last_line_empty = text == "";
					if (text == "") {
						span = doc.createElement('br');
					} else {
						span = doc.createElement('span');
						span.textContent = text + "\n";
						span.style.fontFamily = 'monospace';
						span.style.whiteSpace = 'pre';
						span.style.color = 'red';
					}
					doc.firstChild.appendChild(span);
					if (doc.body)
						ys.window.scrollTo(0, doc.body.scrollHeight);
					else
						ys.window.scrollBy(0, 100);
				} else
				if (!ys.logprint)
					console.log(text);
			},
		};

		ys.write = function(text) {
			ys.print_buffer += text + "\n";
			ys.last_line_empty = text == "";
			span = doc.createElement('span');
			span.textContent = text + "\n";
			span.style.fontFamily = 'monospace';
			span.style.whiteSpace = 'pre';
			doc.firstChild.appendChild(span);
			if (doc.body)
				ys.window.scrollTo(0, doc.body.scrollHeight);
			else
				ys.window.scrollBy(0, 100);
		}

		ys.prompt = function() {
			return mod.ccall('prompt', 'string', [], [])
		}

		ys.run = function(cmd) {
			ys.print_buffer = "";
			if (ys.echo) {
				if (!ys.last_line_empty)
					ys.write("");
				ys.write(ys.prompt() + cmd);
			}
			try {
				mod.ccall('run', '', ['string'], [cmd]);
			} catch (e) {
				ys.errmsg = mod.ccall('errmsg', 'string', [], []);
			}
			return ys.print_buffer;
		}

		ys.read_file = function(filename) {
			try {
				return ys.window.FS.readFile(filename, {encoding: 'utf8'});
			} catch (e) {
				return "";
			}
		}

		ys.write_file = function(filename, text) {
			return ys.window.FS.writeFile(filename, text, {encoding: 'utf8'});
		}

		ys.read_dir = function(dirname) {
			return ys.window.FS.readdir(dirname);
		}

		ys.remove_file = function(filename) {
			try {
				ys.window.FS.unlink(filename);
			} catch (e) { }
		}

		doc.open();
		doc.write('<script type="text/javascript" src="' + this.url_prefix + 'yosys.js"></' + 'script>');
		doc.close();

		if (on_ready || ys.init_script) {
			function check_ready() {
				if (ys.ready && ys.YosysJS.viz_ready) {
					if (ys.init_script) {
						ys.write_file("/script.ys", ys.init_script);
						ys.run("script /script.ys");
					}
					if (on_ready)
						on_ready(ys);
				} else
					window.setTimeout(check_ready, 100);
			}
			window.setTimeout(check_ready, 100);
		}

		return ys;
	}

	this.create_worker = function(on_ready) {
		var ys = new Object();
		ys.YosysJS = this;
		ys.worker = new Worker(this.url_prefix + 'yosyswrk.js');
		ys.callback_idx = 1;
		ys.callback_cache = {};
		ys.errmsg = "";

		ys.callback_cache[0] = on_ready;
		on_ready = null;

		ys.worker.onmessage = function(e) {
			var response = e.data[0];
			var callback = ys.callback_cache[response.idx];
			delete ys.callback_cache[response.idx];
			if ("errmsg" in response) ys.errmsg = response.errmsg;
			if (callback) callback.apply(null, response.args);
		}

		ys.run = function(cmd, callback) {
			var request = {
				"idx": ys.callback_idx,
				"mode": "run",
				"cmd": cmd
			};

			ys.callback_cache[ys.callback_idx++] = callback;
			ys.worker.postMessage([request]);
		}

		ys.read_file = function(filename, callback) {
			var request = {
				"idx": ys.callback_idx,
				"mode": "read_file",
				"filename": filename
			};

			ys.callback_cache[ys.callback_idx++] = callback;
			ys.worker.postMessage([request]);
		}

		ys.write_file = function(filename, text, callback) {
			var request = {
				"idx": ys.callback_idx,
				"mode": "write_file",
				"filename": filename,
				"text": text
			};

			ys.callback_cache[ys.callback_idx++] = callback;
			ys.worker.postMessage([request]);
		}

		ys.read_dir = function(dirname, callback) {
			var request = {
				"idx": ys.callback_idx,
				"mode": "read_dir",
				"dirname": dirname
			};

			ys.callback_cache[ys.callback_idx++] = callback;
			ys.worker.postMessage([request]);
		}

		ys.remove_file = function(filename, callback) {
			var request = {
				"idx": ys.callback_idx,
				"mode": "remove_file",
				"filename": filename
			};

			ys.callback_cache[ys.callback_idx++] = callback;
			ys.worker.postMessage([request]);
		}

		ys.verbose = function(value, callback) {
			var request = {
				"idx": ys.callback_idx,
				"mode": "verbose",
				"value": value
			};

			ys.callback_cache[ys.callback_idx++] = callback;
			ys.worker.postMessage([request]);
		}

		return ys;
	}
}
