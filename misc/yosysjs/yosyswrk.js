var Module = {};
var verbose_mode = false;
var text_buffer = "";

Module["printErr"] = Module["print"] = function(text) {
	if (verbose_mode)
		console.log(text);
	text_buffer += text + "\n";
}

importScripts('yosys.js');

onmessage = function(e) {
	var request = e.data[0];
	var response = { "idx": request.idx, "args": [] };

	if (request.mode == "run") {
		response["errmsg"] = "";
		try {
			text_buffer = "";
			Module.ccall('run', '', ['string'], [request.cmd]);
		} catch (e) {
			response.errmsg = Module.ccall('errmsg', 'string', [], []);
		}
		response.args.push(text_buffer);
		response.args.push(response.errmsg);
		text_buffer = "";
	}

	if (request.mode == "read_file") {
		try {
			response.args.push(FS.readFile(request.filename, {encoding: 'utf8'}));
		} catch (e) { }
	}

	if (request.mode == "write_file") {
		try {
			FS.writeFile(request.filename, request.text, {encoding: 'utf8'});
		} catch (e) { }
	}

	if (request.mode == "read_dir") {
		try {
			response.args.push(FS.readdir(request.dirname));
		} catch (e) { }
	}

	if (request.mode == "remove_file") {
		try {
			FS.unlink(request.filename);
		} catch (e) { }
	}

	if (request.mode == "verbose") {
		if (request.value)
			console.log(text_buffer);
		verbose_mode = request.value;
	}

	postMessage([response]);
}

postMessage([{ "idx": 0, "args": [] }]);
