importScripts('yosys.js');

onmessage = function(e) {
	var request = e.data[0];
	var response = { "idx": request.idx, "args": [] };

	if (request.mode == "run") {
		try {
			Module.ccall('run', '', ['string'], [request.cmd]);
			response.args.push("");
		} catch (e) {
			response.args.push(mod.ccall('errmsg', 'string', [], []));
		}
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

	postMessage([response]);
}

postMessage([{ "idx": 0, "args": [] }]);
