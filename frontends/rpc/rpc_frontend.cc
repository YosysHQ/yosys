/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019  whitequark <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

// The reason the -path mode of connect_rpc uses byte-oriented and not message-oriented sockets, even though
// it is a message-oriented interface, is that the system can place various limits on the message size, which
// are not always transparent or easy to change. Given that generated HDL code get be extremely large, it is
// unwise to rely on those limits being large enough, and using byte-oriented sockets is guaranteed to work.

#ifndef _WIN32
#include <unistd.h>
#include <spawn.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <sys/un.h>
extern char **environ;
#endif

#include "libs/json11/json11.hpp"
#include "libs/sha1/sha1.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

#if defined(_WIN32)
static std::wstring str2wstr(const std::string &in) {
    if(in == "") return L"";
    std::wstring out;
    out.resize(MultiByteToWideChar(/*CodePage=*/CP_UTF8, /*dwFlags=*/0, /*lpMultiByteStr=*/&in[0], /*cbMultiByte=*/(int)in.length(), /*lpWideCharStr=*/NULL, /*cchWideChar=*/0));
    int written = MultiByteToWideChar(/*CodePage=*/CP_UTF8, /*dwFlags=*/0, /*lpMultiByteStr=*/&in[0], /*cbMultiByte=*/(int)in.length(), /*lpWideCharStr=*/&out[0], /*cchWideChar=*/(int)out.length());
    log_assert(written == (int)out.length());
    return out;
}

static std::string wstr2str(const std::wstring &in) {
	if(in == L"") return "";
	std::string out;
	out.resize(WideCharToMultiByte(/*CodePage=*/CP_UTF8, /*dwFlags=*/0, /*lpWideCharStr=*/&in[0], /*cchWideChar=*/(int)in.length(), /*lpMultiByteStr=*/NULL, /*cbMultiByte=*/0, /*lpDefaultChar=*/NULL, /*lpUsedDefaultChar=*/NULL));
	int written = WideCharToMultiByte(/*CodePage=*/CP_UTF8, /*dwFlags=*/0, /*lpWideCharStr=*/&in[0], /*cchWideChar=*/(int)in.length(), /*lpMultiByteStr=*/&out[0], /*cbMultiByte=*/(int)out.length(), /*lpDefaultChar=*/NULL, /*lpUsedDefaultChar=*/NULL);
	log_assert(written == (int)out.length());
	return out;
}

static std::string get_last_error_str() {
	DWORD last_error = GetLastError();
	LPWSTR out_w;
	DWORD size_w = FormatMessageW(/*dwFlags=*/FORMAT_MESSAGE_FROM_SYSTEM|FORMAT_MESSAGE_ALLOCATE_BUFFER|FORMAT_MESSAGE_IGNORE_INSERTS, /*lpSource=*/NULL, /*dwMessageId=*/last_error, /*dwLanguageId=*/0, /*lpBuffer=*/(LPWSTR)&out_w, /*nSize=*/0, /*Arguments=*/NULL);
	if (size_w == 0)
		return std::to_string(last_error);
	std::string out = wstr2str(std::wstring(out_w, size_w));
	LocalFree(out_w);
	return out;
}
#endif

using json11::Json;

struct RpcServer {
	std::string name;

	RpcServer(const std::string &name) : name(name) { }
	virtual ~RpcServer() { }

	virtual void write(const std::string &data) = 0;
	virtual std::string read() = 0;

	Json call(const Json &json_request) {
		std::string request;
		json_request.dump(request);
		request += '\n';
		log_debug("RPC frontend request: %s", request.c_str());
		write(request);

		std::string response = read();
		log_debug("RPC frontend response: %s", response.c_str());
		std::string error;
		Json json_response = Json::parse(response, error);
		if (json_response.is_null())
			log_cmd_error("parsing JSON failed: %s\n", error.c_str());
		if (json_response["error"].is_string())
			log_cmd_error("RPC frontend returned an error: %s\n", json_response["error"].string_value().c_str());
		return json_response;
	}

	std::vector<std::string> get_module_names() {
		Json response = call(Json::object {
			{ "method", "modules" },
		});
		bool is_valid = true;
		std::vector<std::string> modules;
		if (response["modules"].is_array()) {
			for (auto &json_module : response["modules"].array_items()) {
				if (json_module.is_string())
					modules.push_back(json_module.string_value());
				else is_valid = false;
			}
		} else is_valid = false;
		if (!is_valid)
			log_cmd_error("RPC frontend returned malformed response: %s\n", response.dump().c_str());
		return modules;
	}

	std::pair<std::string, std::string> derive_module(const std::string &module, const dict<RTLIL::IdString, RTLIL::Const> &parameters) {
		Json::object json_parameters;
		for (auto &param : parameters) {
			std::string type, value;
			if (param.second.flags & RTLIL::CONST_FLAG_REAL) {
				type = "real";
				value = param.second.decode_string();
			} else if (param.second.flags & RTLIL::CONST_FLAG_STRING) {
				type = "string";
				value = param.second.decode_string();
			} else if ((param.second.flags & ~RTLIL::CONST_FLAG_SIGNED) == RTLIL::CONST_FLAG_NONE) {
				type = (param.second.flags & RTLIL::CONST_FLAG_SIGNED) ? "signed" : "unsigned";
				value = param.second.as_string();
			} else
				log_cmd_error("Unserializable constant flags 0x%x\n", param.second.flags);
			json_parameters[param.first.str()] = Json::object {
				{ "type", type },
				{ "value", value },
			};
		}
		Json response = call(Json::object {
			{ "method", "derive" },
			{ "module", module },
			{ "parameters", json_parameters },
		});
		bool is_valid = true;
		std::string frontend, source;
		if (response["frontend"].is_string())
			frontend = response["frontend"].string_value();
		else is_valid = false;
		if (response["source"].is_string())
			source = response["source"].string_value();
		else is_valid = false;
		if (!is_valid)
			log_cmd_error("RPC frontend returned malformed response: %s\n", response.dump().c_str());
		return std::make_pair(frontend, source);
	}
};

struct RpcModule : RTLIL::Module {
	std::shared_ptr<RpcServer> server;

	RTLIL::IdString derive(RTLIL::Design *design, dict<RTLIL::IdString, RTLIL::Const> parameters, bool /*mayfail*/) YS_OVERRIDE {
		std::string stripped_name = name.str();
		if (stripped_name.compare(0, 9, "$abstract") == 0)
			stripped_name = stripped_name.substr(9);
		log_assert(stripped_name[0] == '\\');

		log_header(design, "Executing RPC frontend `%s' for module `%s'.\n", server->name.c_str(), stripped_name.c_str());

		std::string parameter_info;
		for (auto &param : parameters) {
			log("Parameter %s = %s\n", param.first.c_str(), log_signal(RTLIL::SigSpec(param.second)));
			parameter_info += stringf("%s=%s", param.first.c_str(), log_signal(RTLIL::SigSpec(param.second)));
		}

		std::string derived_name;
		if (parameters.empty())
			derived_name = stripped_name;
		else if (parameter_info.size() > 60)
			derived_name = "$paramod$" + sha1(parameter_info) + stripped_name;
		else
			derived_name = "$paramod" + stripped_name + parameter_info;

		if (design->has(derived_name)) {
			log("Found cached RTLIL representation for module `%s'.\n", derived_name.c_str());
		} else {
			std::string command, input;
			std::tie(command, input) = server->derive_module(stripped_name.substr(1), parameters);

			std::istringstream input_stream(input);
			RTLIL::Design *derived_design = new RTLIL::Design;
			Frontend::frontend_call(derived_design, &input_stream, "<rpc>" + derived_name.substr(8), command);
			derived_design->check();

			dict<std::string, std::string> name_mangling;
			bool found_derived_top = false;
			for (auto module : derived_design->modules()) {
				std::string original_name = module->name.str();
				if (original_name == stripped_name) {
					found_derived_top = true;
					name_mangling[original_name] = derived_name;
				} else {
					name_mangling[original_name] = derived_name + module->name.str();
				}
			}
			if (!found_derived_top)
				log_cmd_error("RPC frontend did not return requested module `%s`!\n", stripped_name.c_str());

			for (auto module : derived_design->modules())
				for (auto cell : module->cells())
					if (name_mangling.count(cell->type.str()))
						cell->type = name_mangling[cell->type.str()];

			for (auto module : derived_design->modules_) {
				std::string mangled_name = name_mangling[module.first.str()];

				log("Importing `%s' as `%s'.\n", log_id(module.first), log_id(mangled_name));

				module.second->name = mangled_name;
				module.second->design = design;
				module.second->attributes.erase("\\top");
				design->modules_[mangled_name] = module.second;
				derived_design->modules_.erase(module.first);
			}

			delete derived_design;
		}

		return derived_name;
	}

	RTLIL::Module *clone() const YS_OVERRIDE {
		RpcModule *new_mod = new RpcModule;
		new_mod->server = server;
		cloneInto(new_mod);
		return new_mod;
	}
};

#if defined(_WIN32)

#if defined(_MSC_VER)
#include <BaseTsd.h>
typedef SSIZE_T ssize_t;
#endif

struct HandleRpcServer : RpcServer {
	HANDLE hsend, hrecv;

	HandleRpcServer(const std::string &name, HANDLE hsend, HANDLE hrecv)
		: RpcServer(name), hsend(hsend), hrecv(hrecv) { }

	void write(const std::string &data) YS_OVERRIDE {
		log_assert(data.length() >= 1 && data.find('\n') == data.length() - 1);
		ssize_t offset = 0;
		do {
			DWORD data_written;
			if (!WriteFile(hsend, &data[offset], data.length() - offset, &data_written, /*lpOverlapped=*/NULL))
				log_cmd_error("WriteFile failed: %s\n", get_last_error_str().c_str());
			offset += data_written;
		} while(offset < (ssize_t)data.length());
	}

	std::string read() YS_OVERRIDE {
		std::string data;
		ssize_t offset = 0;
		while (data.length() == 0 || data[data.length() - 1] != '\n') {
			data.resize(data.length() + 1024);
			DWORD data_read;
			if (!ReadFile(hrecv, &data[offset], data.length() - offset, &data_read, /*lpOverlapped=*/NULL))
				log_cmd_error("ReadFile failed: %s\n", get_last_error_str().c_str());
			offset += data_read;
			data.resize(offset);
			size_t term_pos = data.find('\n', offset);
			if (term_pos != data.length() - 1 && term_pos != std::string::npos)
				log_cmd_error("read failed: more than one response\n");
		}
		return data;
	}

	~HandleRpcServer() {
		CloseHandle(hsend);
		if (hrecv != hsend)
			CloseHandle(hrecv);
	}
};

#else

struct FdRpcServer : RpcServer {
	int fdsend, fdrecv;
	pid_t pid;

	FdRpcServer(const std::string &name, int fdsend, int fdrecv, pid_t pid = -1)
		: RpcServer(name), fdsend(fdsend), fdrecv(fdrecv), pid(pid) { }

	void check_pid() {
		if (pid == -1) return;
		// If we're communicating with a process, check that it's still running, or we may get killed with SIGPIPE.
		pid_t wait_result = ::waitpid(pid, NULL, WNOHANG);
		if (wait_result == -1)
			log_cmd_error("waitpid failed: %s\n", strerror(errno));
		if (wait_result == pid)
			log_cmd_error("RPC frontend terminated unexpectedly\n");
	}

	void write(const std::string &data) YS_OVERRIDE {
		log_assert(data.length() >= 1 && data.find('\n') == data.length() - 1);
		ssize_t offset = 0;
		do {
			check_pid();
			ssize_t result = ::write(fdsend, &data[offset], data.length() - offset);
			if (result == -1)
				log_cmd_error("write failed: %s\n", strerror(errno));
			offset += result;
		} while(offset < (ssize_t)data.length());
	}

	std::string read() YS_OVERRIDE {
		std::string data;
		ssize_t offset = 0;
		while (data.length() == 0 || data[data.length() - 1] != '\n') {
			data.resize(data.length() + 1024);
			check_pid();
			ssize_t result = ::read(fdrecv, &data[offset], data.length() - offset);
			if (result == -1)
				log_cmd_error("read failed: %s\n", strerror(errno));
			offset += result;
			data.resize(offset);
			size_t term_pos = data.find('\n', offset);
			if (term_pos != data.length() - 1 && term_pos != std::string::npos)
				log_cmd_error("read failed: more than one response\n");
		}
		return data;
	}

	~FdRpcServer() {
		close(fdsend);
		if (fdrecv != fdsend)
			close(fdrecv);
	}
};

#endif

// RpcFrontend does not inherit from Frontend since it does not read files.
struct RpcFrontend : public Pass {
	RpcFrontend() : Pass("connect_rpc", "connect to RPC frontend") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    connect_rpc -exec <command> [args...]\n");
		log("    connect_rpc -path <path>\n");
		log("\n");
		log("Load modules using an out-of-process frontend.\n");
		log("\n");
		log("    -exec <command> [args...]\n");
		log("        run <command> with arguments [args...]. send requests on stdin, read\n");
		log("        responses from stdout.\n");
		log("\n");
		log("    -path <path>\n");
		log("        connect to Unix domain socket at <path>. (Unix)\n");
		log("        connect to bidirectional byte-type named pipe at <path>. (Windows)\n");
		log("\n");
		log("A simple JSON-based, newline-delimited protocol is used for communicating with\n");
		log("the frontend. Yosys requests data from the frontend by sending exactly 1 line\n");
		log("of JSON. Frontend responds with data or error message by replying with exactly\n");
		log("1 line of JSON as well.\n");
		log("\n");
		log("    -> {\"method\": \"modules\"}\n");
		log("    <- {\"modules\": [\"<module-name>\", ...]}\n");
		log("    <- {\"error\": \"<error-message>\"}\n");
		log("        request for the list of modules that can be derived by this frontend.\n");
		log("        the 'hierarchy' command will call back into this frontend if a cell\n");
		log("        with type <module-name> is instantiated in the design.\n");
		log("\n");
		log("    -> {\"method\": \"derive\", \"module\": \"<module-name\">, \"parameters\": {\n");
		log("        \"<param-name>\": {\"type\": \"[unsigned|signed|string|real]\",\n");
		log("                           \"value\": \"<param-value>\"}, ...}}\n");
		log("    <- {\"frontend\": \"[ilang|verilog|...]\",\"source\": \"<source>\"}}\n");
		log("    <- {\"error\": \"<error-message>\"}\n");
		log("        request for the module <module-name> to be derived for a specific set of\n");
		log("        parameters. <param-name> starts with \\ for named parameters, and with $\n");
		log("        for unnamed parameters, which are numbered starting at 1.<param-value>\n");
		log("        for integer parameters is always specified as a binary string of unlimited\n");
		log("        precision. the <source> returned by the frontend is hygienically parsed\n");
		log("        by a built-in Yosys <frontend>, allowing the RPC frontend to return any\n");
		log("        convenient representation of the module. the derived module is cached,\n");
		log("        so the response should be the same whenever the same set of parameters\n");
		log("        is provided.\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Connecting to RPC frontend.\n");

		std::vector<std::string> command;
		std::string path;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-exec" && argidx+1 < args.size()) {
				command.insert(command.begin(), args.begin() + argidx + 1, args.end());
				continue;
			}
			if (arg == "-path" && argidx+1 < args.size()) {
				path = args[argidx+1];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if ((!command.empty()) + (!path.empty()) != 1)
			log_cmd_error("Exactly one of -exec, -unix must be specified.\n");

		std::shared_ptr<RpcServer> server;
		if (!command.empty()) {
			std::string command_line;
			bool first = true;
			for (auto &arg : command) {
				if (!first) command_line += ' ';
				command_line += arg;
				first = false;
			}

#ifdef _WIN32
			std::wstring command_w = str2wstr(command[0]);
			std::wstring command_path_w;
			std::wstring command_line_w = str2wstr(command_line);
			DWORD command_path_len_w;
			SECURITY_ATTRIBUTES pipe_attr = {};
			HANDLE send_r = NULL, send_w = NULL, recv_r = NULL, recv_w = NULL;
			STARTUPINFOW startup_info = {};
			PROCESS_INFORMATION proc_info = {};

			command_path_len_w = SearchPathW(/*lpPath=*/NULL, /*lpFileName=*/command_w.c_str(), /*lpExtension=*/L".exe", /*nBufferLength=*/0, /*lpBuffer=*/NULL, /*lpFilePart=*/NULL);
			if (command_path_len_w == 0) {
				log_error("SearchPathW failed: %s\n", get_last_error_str().c_str());
				goto cleanup_exec;
			}
			command_path_w.resize(command_path_len_w - 1);
			command_path_len_w = SearchPathW(/*lpPath=*/NULL, /*lpFileName=*/command_w.c_str(), /*lpExtension=*/L".exe", /*nBufferLength=*/command_path_len_w, /*lpBuffer=*/&command_path_w[0], /*lpFilePart=*/NULL);
			log_assert(command_path_len_w == command_path_w.length());

			pipe_attr.nLength = sizeof(pipe_attr);
			pipe_attr.bInheritHandle = TRUE;
			pipe_attr.lpSecurityDescriptor = NULL;
			if (!CreatePipe(&send_r, &send_w, &pipe_attr, /*nSize=*/0)) {
				log_error("CreatePipe failed: %s\n", get_last_error_str().c_str());
				goto cleanup_exec;
			}
			if (!SetHandleInformation(send_w, HANDLE_FLAG_INHERIT, 0)) {
				log_error("SetHandleInformation failed: %s\n", get_last_error_str().c_str());
				goto cleanup_exec;
			}
			if (!CreatePipe(&recv_r, &recv_w, &pipe_attr, /*nSize=*/0)) {
				log_error("CreatePipe failed: %s\n", get_last_error_str().c_str());
				goto cleanup_exec;
			}
			if (!SetHandleInformation(recv_r, HANDLE_FLAG_INHERIT, 0)) {
				log_error("SetHandleInformation failed: %s\n", get_last_error_str().c_str());
				goto cleanup_exec;
			}

			startup_info.cb = sizeof(startup_info);
			startup_info.hStdInput = send_r;
			startup_info.hStdOutput = recv_w;
			startup_info.hStdError = GetStdHandle(STD_ERROR_HANDLE);
			startup_info.dwFlags |= STARTF_USESTDHANDLES;
			if (!CreateProcessW(/*lpApplicationName=*/command_path_w.c_str(), /*lpCommandLine=*/&command_line_w[0], /*lpProcessAttributes=*/NULL, /*lpThreadAttributes=*/NULL, /*bInheritHandles=*/TRUE, /*dwCreationFlags=*/0, /*lpEnvironment=*/NULL, /*lpCurrentDirectory=*/NULL, &startup_info, &proc_info)) {
				log_error("CreateProcessW failed: %s\n", get_last_error_str().c_str());
				goto cleanup_exec;
			}
			CloseHandle(proc_info.hProcess);
			CloseHandle(proc_info.hThread);

			server = std::make_shared<HandleRpcServer>(path, send_w, recv_r);
			send_w = NULL;
			recv_r = NULL;

cleanup_exec:
			if (send_r != NULL) CloseHandle(send_r);
			if (send_w != NULL) CloseHandle(send_w);
			if (recv_r != NULL) CloseHandle(recv_r);
			if (recv_w != NULL) CloseHandle(recv_w);
#else
			std::vector<char *> argv;
			int send[2] = {-1,-1}, recv[2] = {-1,-1};
			posix_spawn_file_actions_t file_actions, *file_actions_p = NULL;
			pid_t pid;

			for (auto &arg : command)
				argv.push_back(&arg[0]);
			argv.push_back(nullptr);

			if (pipe(send) != 0) {
				log_error("pipe failed: %s\n", strerror(errno));
				goto cleanup_exec;
			}
			if (pipe(recv) != 0) {
				log_error("pipe failed: %s\n", strerror(errno));
				goto cleanup_exec;
			}

			if (posix_spawn_file_actions_init(&file_actions) != 0) {
				log_error("posix_spawn_file_actions_init failed: %s\n", strerror(errno));
				goto cleanup_exec;
			}
			file_actions_p = &file_actions;
			if (posix_spawn_file_actions_adddup2(file_actions_p, send[0], STDIN_FILENO) != 0) {
				log_error("posix_spawn_file_actions_adddup2 failed: %s\n", strerror(errno));
				goto cleanup_exec;
			}
			if (posix_spawn_file_actions_addclose(file_actions_p, send[1]) != 0) {
				log_error("posix_spawn_file_actions_addclose failed: %s\n", strerror(errno));
				goto cleanup_exec;
			}
			if (posix_spawn_file_actions_adddup2(file_actions_p, recv[1], STDOUT_FILENO) != 0) {
				log_error("posix_spawn_file_actions_adddup2 failed: %s\n", strerror(errno));
				goto cleanup_exec;
			}
			if (posix_spawn_file_actions_addclose(file_actions_p, recv[0]) != 0) {
				log_error("posix_spawn_file_actions_addclose failed: %s\n", strerror(errno));
				goto cleanup_exec;
			}

			if (posix_spawnp(&pid, argv[0], file_actions_p, /*attrp=*/NULL, argv.data(), environ) != 0) {
				log_error("posix_spawnp failed: %s\n", strerror(errno));
				goto cleanup_exec;
			}

			server = std::make_shared<FdRpcServer>(command_line, send[1], recv[0], pid);
			send[1] = -1;
			recv[0] = -1;

cleanup_exec:
			if (send[0] != -1) close(send[0]);
			if (send[1] != -1) close(send[1]);
			if (recv[0] != -1) close(recv[0]);
			if (recv[1] != -1) close(recv[1]);
			if (file_actions_p != NULL)
				posix_spawn_file_actions_destroy(file_actions_p);
#endif
		} else if (!path.empty()) {
#ifdef _WIN32
			std::wstring path_w = str2wstr(path);
			HANDLE h;

			h = CreateFileW(path_w.c_str(), GENERIC_READ|GENERIC_WRITE, /*dwShareMode=*/0, /*lpSecurityAttributes=*/NULL, /*dwCreationDisposition=*/OPEN_EXISTING, /*dwFlagsAndAttributes=*/0, /*hTemplateFile=*/NULL);
			if (h == INVALID_HANDLE_VALUE) {
				log_error("CreateFileW failed: %s\n", get_last_error_str().c_str());
				goto cleanup_path;
			}

			server = std::make_shared<HandleRpcServer>(path, h, h);

cleanup_path:
			;
#else
			struct sockaddr_un addr;
			addr.sun_family = AF_UNIX;
			strncpy(addr.sun_path, path.c_str(), sizeof(addr.sun_path) - 1);

			int fd = socket(AF_UNIX, SOCK_STREAM, 0);
			if (fd == -1) {
				log_error("socket failed: %s\n", strerror(errno));
				goto cleanup_path;
			}

			if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) != 0) {
				log_error("connect failed: %s\n", strerror(errno));
				goto cleanup_path;
			}

			server = std::make_shared<FdRpcServer>(path, fd, fd);
			fd = -1;

cleanup_path:
			if (fd != -1) close(fd);
#endif
		}

		if (!server)
			log_cmd_error("Failed to connect to RPC frontend.\n");

		for (auto &module_name : server->get_module_names()) {
			log("Linking module `%s'.\n", module_name.c_str());
			RpcModule *module = new RpcModule;
			module->name = "$abstract\\" + module_name;
			module->server = server;
			design->add(module);
		}
	}
} RpcFrontend;

YOSYS_NAMESPACE_END
