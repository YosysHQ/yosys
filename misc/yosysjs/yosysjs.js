var YosysJS = new function() {
	this.script_element = document.currentScript;
	this.viz_element = undefined;

	this.url_prefix = this.script_element.src.replace(/[^/]+$/, '')

	this.load_viz = function() {
		if (this.viz_element)
			return;

		this.viz_element = document.createElement('iframe')
		this.viz_element.style.display = 'none'
		document.body.appendChild(this.viz_element);

		this.viz_element.contentWindow.document.open()
		this.viz_element.contentWindow.document.write('<script type="text/javascript" src="' + this.url_prefix + 'viz.js"></' + 'script>');
		this.viz_element.contentWindow.document.close()
	}

	this.dot_to_svg = function(dot_text) {
		return this.viz_element.contentWindow.Viz(dot_text, "svg");
	}

	this.dot_into_svg = function(dot_text, svg_element) {
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
		ys.init_script = "";
		ys.ready = false;
		ys.verbose = false;
		ys.echo = false;

		if (typeof(reference_element) == 'string')
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
			document.body.appendChild(ys.iframe_element);
		}

		var return_buffer = "";
		var last_line_empty = false;

		var win = ys.iframe_element.contentWindow;
		var doc = ys.iframe_element.contentWindow.document;
		var mod = ys.iframe_element.contentWindow.Module = {
			print: function(text) {
				return_buffer += text + "\n";
				if (ys.verbose) {
					last_line_empty = text == "";
					span = doc.createElement('span');
					span.textContent = text + "\n";
					span.style.fontFamily = 'monospace';
					span.style.whiteSpace = 'pre';
					doc.body.appendChild(span);
					win.scrollTo(0, doc.body.scrollHeight)
				}
				ys.ready = true;
			},
			printErr: function(text) {
				return_buffer += text + "\n";
				last_line_empty = text == "";
				span = doc.createElement('span');
				span.textContent = text + "\n";
				span.style.fontFamily = 'monospace';
				span.style.whiteSpace = 'pre';
				span.style.color = 'red';
				doc.body.appendChild(span);
				win.scrollTo(0, doc.body.scrollHeight)
			},
		};

		ys.write = function(text) {
			last_line_empty = text == "";
			span = doc.createElement('span');
			span.textContent = text + "\n";
			span.style.fontFamily = 'monospace';
			span.style.whiteSpace = 'pre';
			doc.body.appendChild(span);
			win.scrollTo(0, doc.body.scrollHeight)
		}

		ys.prompt = function() {
			return mod.ccall('prompt', 'string', [], [])
		}

		ys.run = function(cmd) {
			return_buffer = "";
			if (ys.echo) {
				if (!last_line_empty)
					ys.write("");
				ys.write(ys.prompt() + cmd);
			}
			mod.ccall('run', '', ['string'], [cmd]);
			return return_buffer;
		}

		ys.read_file = function(filename) {
			return win.FS.readFile(filename, {encoding: 'utf8'});
		}

		ys.write_file = function(filename, text) {
			return win.FS.writeFile(filename, text, {encoding: 'utf8'});
		}

		ys.read_dir = function(dirname) {
			return win.FS.readdir(dirname);
		}

		el = doc.createElement('script');
		el.type = 'text/javascript';
		el.src = this.url_prefix + 'yosys.js';
		doc.head.appendChild(el);

		if (on_ready || ys.init_script) {
			function check_ready() {
				if (ys.ready) {
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
}
