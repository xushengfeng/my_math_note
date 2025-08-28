type TextMeta = {
	id: string;
	name: string;
	base: string[];
};

function newId() {
	return crypto.randomUUID().slice(0, 8);
}

function getChangedFiles() {
	const x: string[] = ["-c", "core.quotePath=false"];
	const command = new Deno.Command("git", {
		args: [...x, "diff", "--name-only", "HEAD"],
		stdout: "piped",
	});
	const { stdout } = command.outputSync();
	const output = new TextDecoder().decode(stdout);

	const command2 = new Deno.Command("git", {
		args: [...x, "ls-files", "--others", "--exclude-standard"],
		stdout: "piped",
	});
	const { stdout: stdout2 } = command2.outputSync();
	const output2 = new TextDecoder().decode(stdout2);

	return output
		.split("\n")
		.concat(output2.split("\n"))
		.filter((i) => i);
}

function parseMdMeta(content: string) {
	const match = content.match(/---\n([\s\S]*?)\n---/);
	if (match) {
		return JSON.parse(`{${match[1]}}`);
	}
	return null;
}

function updateChapater(paths: string[]) {
	const _metaData = structuredClone(metaData);
	const existIds = new Set<string>(_metaData.text.map((m: any) => m.id));
	for (const path of paths) {
		const content = Deno.readTextFileSync(path);
		const meta = parseMdMeta(content);
		if (!meta) {
			console.warn(`No meta found in ${path}`);
			continue;
		}
		if (!meta.id) {
			continue;
		}
		existIds.add(meta.id);
		const existingIndex = _metaData.text.findIndex(
			(m: any) => m.id === meta.id,
		);
		meta.path = path;
		if (existingIndex !== -1) {
			_metaData.text[existingIndex] = meta;
		} else {
			_metaData.text.push(meta);
		}
	}
	return _metaData;
}

function checkBaseDag(metaData: any) {
	// todo
}

function writeMetaData(data: any) {
	const metaDataPath = "./data.json";
	Deno.writeTextFileSync(metaDataPath, JSON.stringify(data, null, 2) + "\n");
	console.log(`Updated ${metaDataPath}`);
}

const args = Deno.args;
const argsObj: Record<string, string | boolean> = {};
for (let i = 0; i < args.length; i++) {
	const arg = args[i];
	if (arg.startsWith("--")) {
		const key = arg.slice(2);
		const nextArg = args[i + 1];
		if (nextArg && !nextArg.startsWith("--")) {
			argsObj[key] = nextArg;
			i++;
		} else {
			argsObj[key] = true;
		}
	}
}

const metaDataPath = "./data.json";
const metaData = JSON.parse(await Deno.readTextFile(metaDataPath));

if (argsObj.newmeta) {
	let nid = newId();
	while (metaData.text.find((m: any) => m.id === nid)) {
		nid = newId();
	}
	const data: TextMeta = {
		id: nid,
		name: "",
		base: [],
	};
	console.log(
		`---\n${JSON.stringify(data, null, 1)
			.split("\n")
			.slice(1, -1)
			.map((i) => i.slice(1))
			.join("\n")}\n---`,
	);
}

if (argsObj.updatetext) {
	const textPaths = getChangedFiles().filter(
		(i) => i.startsWith("text/") && i.endsWith(".md"),
	);
	const data = updateChapater(textPaths);
	checkBaseDag(data);
	writeMetaData(data);
}
