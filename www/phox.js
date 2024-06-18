
function upload_phox_file(fname, mime="text/plain; charset=x-user-defined") {
    const xhr = new XMLHttpRequest();
    xhr.open('GET', fname, false);
    xhr.overrideMimeType(mime);
    xhr.send();
    if (xhr.status === 200) {
	return xhr.response;
    } else {
	return "";
    }
}

function load_file(fname) {
    restart();
    content = upload_phox_file(fname, "text/plain; charset=UTF-8");
    const el = document.getElementsByClassName('editor')[0];
    el.setContent(content);
}
let out_to_parse = "";

let first_to_load=0;

function addDiv() {
    const el = document.getElementsByClassName('editor')[0];
    const div = document.createElement("div");
    const br = document.createElement("br");
    div.appendChild(br);
    el.appendChild(div);
}

function getSpan(i) {
    const el = document.getElementsByClassName('editor')[0];
    let l = 0; let s = 0;
    while (l < el.children) {
	const line = el.children[l].children;
	if (i < line.length) {
	    i -= line.length; l++;
	} else {
	    return line[i];
	}
    }
    return null;
}

function* iterSpan(start=0) {
    const el = document.getElementsByClassName('editor')[0];
    let l = 0; let s = 0; let cur = 0;
    while (l < el.children.length) {
	const line = el.children[l].children;
	if (start >= line.length) {
	    start -= line.length; l++;
	    cur += line.length;
	} else {
	    if (start == line.length - 1 && l == el.children.length - 1) {
		return [cur+start, line[start]];
	    } else {
		yield [cur+start, line[start]];
		start += 1;
	    }
	}
    }
    return null;
}

function getDot(str) {
    return str.innerText.search(/[.](\s|$)/g);
}

greenElements = [];

function undo() {
    phox_worker.postMessage("undo.\n");
}

function ungreen(green) {
    const elts = green.is_goal?green.tbls:[green.tbl];
    for (tbls of elts) {
	for (tbl of tbls) {
	    tbl[1].style.backgroundColor = "white";
	    tbl[1].contentEditable = "inherit";
	    first_to_load = tbl[0];
	}
    }
}

let phox_worker = null;

function restart() {
    if (phox_worker) phox_worker.terminate();
    const goals = document.getElementById("goals");
    goals.style.display = "none";
    for (green of greenElements) {
	ungreen(green);
    }
    greenElements = [];
    first_to_load = 0;
    waiting=[];
    last_waiting = 0;
    out_to_parse = "";
    phox_worker = new Worker('phox.bc.js');
    phox_worker.onmessage = (e) => {
	const s = e.data;
	console.log("message:",s);
	if (s.search(/[%>]PhoX[%>]/g) >= 0) {
	    const in_goal = s[0] == "%";
	    treatOut(out_to_parse, in_goal, last_waiting);
	    out_to_parse = "";
	    trySend();
	} else {
	    out_to_parse += s;
	}
    };
}

function treatOut(s, in_goal, waiting) {
    console.log("treatOut:",s,in_goal);
    if (s.search(/Error/) >= 0) {
	console.log("error");
	const out = document.getElementById("output");
	out.value = s;
	out.style.backgroundColor = "rgba(255,200,200,255)";
    } else {
	console.log("setBackground");
	const out   = document.getElementById("output");
	out.style.backgroundColor = "rgba(200,200,20à,255)";
	if (in_goal) {
	    const goals = document.getElementById("goals");
	    goals.style.display = "block";
	    goals.value = s;
	} else {
	    goals.style.display = "none";
	    out.value = s;
	}
	const undo = s.search(/undo: ([^\n]+)/);
	//console.log("undo:", greenElements);
	if (undo >= 0) {
	    if (in_goal && greenElements.length > 0
		&& greenElements[greenElements.length - 1].is_goal) {
		const elts = greenElements[greenElements.length - 1].tbls.pop();
		for (tbl of elts) {
		    tbl[1].style.backgroundColor = null;
		    tbl[1].contentEditable = "false";
		    first_to_load = tbl[0];
		}
		if (elts.length == 0) {
		    grrenElements.pop();
		}
	    } else {
		unGreen(greenElements.pop());
	    }
	} else {
	    const spans = iterSpan(first_to_load);
	    const elts = [];
	    if (in_goal) {
		if (greenElements[greenElements.length - 1].is_goal) {
		    const tbl = greenElements[greenElements.length - 1].tbls.push(elts);
		} else {
		    greenElements.push({is_goal: true, tbls: [elts]});
		}
	    } else {
		greenElements.push({is_goal: false, tbl: elts});
	    }
	    while (tbl = spans.next().value) {
		if (tbl[0] >= waiting) break;
		tbl[1].style.backgroundColor = "lightgreen";
		tbl[1].contentEditable = "false";
		elts.push(tbl);
	    }
	    //console.log("do:", greenElements);
	    first_to_load = waiting;
	}
    }
}

function getNextCommand(index = first_to_load) {
    let res = "";
    let pos = 0;
    let next = null;
    const spans = iterSpan(index);
    while (next = spans.next()) {
	pos = next.value[0];
	let line = next.value[1];
	console.log("line:", line, line.innerText);
	if (getDot(line) >= 0) {
	    res += line.innerText + '\n';
	    console.log(res);
	    break;
	} else {
	    res += line.innerText + ' ';
	    console.log(res);
	}
    }
    if (next.done) addDiv();
    return { txt: res, span: next.value[1], index: pos + 1 }
}

waiting = [];
last_waiting = 0;

function sendNextCommand() {
    let cmd = getNextCommand();
    waiting.push(cmd);
    trySend();
}

function trySend() {
    console.log("queue: ", waiting.length);
    if (waiting.length > 0) {
	cmd = waiting.shift();
	console.log("current: ", cmd, cmd.txt);
	if (cmd.txt.length > 0) {
	    console.log('send: ', JSON.stringify(cmd.txt));
	    last_waiting = cmd.index;
	    phox_worker.postMessage(cmd.txt);
	}
    }
}

function goTo() {
    const el = document.getElementsByClassName('editor')[0]; // assume one editor
    el.focus();
    const span = el.caret().span;
    console.log("span target: ", span);
    index = first_to_load;
    while(true) {
	cmd = getNextCommand(index);
	waiting.push(cmd);
	if (cmd.span == span) break;
	index = cmd.index
    }
    trySend();
}

function setMenus() {
    const header = document.getElementById('header');
    for (menu of phoxMenus) {
	const sel = document.createElement("select");
	const opt = document.createElement("option");
	opt.innerText = menu.folder;
	sel.appendChild(opt);
	sel.addEventListener('change', (e) => {
	    const index = sel.selectedIndex;
	    load_file(sel.children[index].value) });
	for (file of menu.files) {
	    const opt = document.createElement("option");
	    opt.innerText = file;
	    opt.value = menu.folder + "/" + file;
	    sel.appendChild(opt);
	}
	header.appendChild(sel);
    }
}

window.onload = (() => {
    setMenus();
    const out = document.getElementById("output");
    out.value = "";
    const el = document.getElementsByClassName('editor')[0]; // assume one editor
    // Turn div into an editor
    el.focus();
    editor(el);
    restart();
});
