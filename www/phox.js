
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
    const content = upload_phox_file(fname, "text/plain; charset=UTF-8");
    const el = document.getElementsByClassName('editor')[0];
    el.setContent(content);
}
let out_to_parse = "";

let first_to_load=0;
let first_to_push=0;

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

function getDot(str, from=0) {
    const s = str.innerText.slice(from);
    const index = s.search(/([.](\s|$))|([(][*])|([*][)])/);
    if (index >= 0) {
	return { index:index+from, kind:s[index] };
    } else {
	return null;
    }
}

greenElements = [];

function undo() {
    const last = greenElements[greenElements.length - 1];
    if (last.is_goal && last.tbls.length > 1)
	phox_worker.postMessage("undo.\n");
    else
	phox_worker.postMessage("abort.\n");
}

function ungreenOne(tbls) {
    for (const tbl of tbls) {
	tbl[1].style.backgroundColor = "white";
	tbl[1].contentEditable = "inherit";
	first_to_load = tbl[0];
	first_to_push = tbl[0];
    }
}

function ungreen(green) {
    const elts = green.is_goal?green.tbls:[green.tbl];
    for (const tbls of elts) {
	ungreenOne(tbls);
    }
}

let phox_worker = null;

function restart() {
    if (phox_worker) phox_worker.terminate();
    const goals = document.getElementById("goals");
    goals.style.display = "none";
    for (let green of greenElements) {
	ungreen(green);
    }
    greenElements = [];
    first_to_load = 0;
    first_to_push = 0;
    waiting=[];
    processing = null;
    out_to_parse = "";
    phox_worker = new Worker('phox.bc.js');
    phox_worker.onmessage = (e) => {
	const s = e.data;
	if (s.search(/[%>]PhoX[%>]/g) >= 0) {
	    const in_goal = s[0] == "%";
	    treatOut(out_to_parse, in_goal);
	    out_to_parse = "";
	    trySend();
	} else {
	    out_to_parse += s;
	}
    };
}

function isScrolledIntoView(el) {
    var rect = el.getBoundingClientRect();
    var elemTop = rect.top;
    var elemBottom = rect.bottom;

    // Only completely visible elements return true:
    var isVisible = (elemTop >= 0) && (elemBottom <= window.innerHeight);
    // Partially visible elements return true:
    //isVisible = elemTop < window.innerHeight && elemBottom >= 0;
    return isVisible;
}

function treatOut(s, in_goal) {
    if (s.search(/Error/) >= 0) {
	const out = document.getElementById("output");
	const goals = document.getElementById("goals");
	out.style.backgroundColor = "rgba(255,200,200,255)";
	out.style.display = "block";
	goals.style.display = "none";
	out.value = s;
	waiting = [];
	const cmd = processing;
	if (cmd) {
	    first_to_load = cmd.indexStart;
	    first_to_push = cmd.indexStart;
	}
	processing = null;

    } else {
	const out   = document.getElementById("output");
	out.style.backgroundColor = "rgba(200,200,20à,255)";
	if (in_goal) {
	    goals.style.display = "block";
	    out.style.display = "none";
	    goals.value = s;
	} else {
	    out.style.display = "block";
	    goals.style.display = "none";
	    out.value = s;
	}
	const undo = s.search(/(undo: ([^\n]+))|(proof aborted)/);
	//console.log("undo:", greenElements);
	if (undo >= 0) {
	    if (in_goal && greenElements.length > 0
		&& greenElements[greenElements.length - 1].is_goal) {
		const elts = greenElements[greenElements.length - 1].tbls.pop();
		ungreenOne(elts);
		if (elts.length == 0) {
		    greenElements.pop();
		}
	    } else {
		ungreen(greenElements.pop());
	    }
	} else {
	    const cmd = processing;
	    if (!cmd) return; // first output at start
	    processing = null;
	    trySend();
	    const spans = iterSpan(first_to_load);
	    const elts = [];
	    if (in_goal) {
		if (greenElements.length > 0 &&
		    greenElements[greenElements.length - 1].is_goal) {
		    const tbl = greenElements[greenElements.length - 1].tbls.push(elts);
		} else {
		    greenElements.push({is_goal: true, tbls: [elts]});
		}
	    } else {
		greenElements.push({is_goal: false, tbl: elts});
	    }
	    let tbl = null;
            let last = null;
	    while (tbl = spans.next().value) {
		if (!tbl || tbl[0] > cmd.indexEnd) break;
                last = tbl[1];
		tbl[1].style.backgroundColor = "lightgreen";
		tbl[1].contentEditable = "false";
		first_to_load = tbl[0]+1;
		elts.push(tbl);
		if (!tbl[1].nextElementSibling &&
		    !tbl[1].parentNode.nextElementSibling) { addDiv(); break; }
	    }
            if (!isScrolledIntoView(last)) {
                last.scrollIntoView({
		    behavior: 'auto',
		    block: 'center',
		    inline: 'center'
		});
            }

	    //console.log("do:", greenElements);
	}
    }

}

function getNextCommand(index = first_to_push, target = null) {
    let res = "";
    let indexStart = null;
    let pos = 0;
    let next = null;
    let prev = null;
    const spans = iterSpan(index);
    let comment_lvl = 0;
    outer:
    while ((prev = spans.next()).value) {
	next = prev;
	if (!next || next.value[1] == target) return null;
	pos = next.value[0];
	if (!indexStart) indexStart = pos;
	let line = next.value[1];
	let from = 0;
	inner:
	while (true) {
	    r = getDot(line, from);
	    if (r && r.kind == '.' && comment_lvl == 0) {
		res += line.innerText + ' \n';
		break outer;
	    } else if (r && r.kind == '(') {
		comment_lvl++;
		from = r.index+1;
	    } else if (r && r.kind == '*' && comment_lvl > 0) {
		comment_lvl--;
		from = r.index+1;
	    } else {
		res += line.innerText;
		if (!next.value[1].nextElementSibling) res+='\n';
		break inner;
	    }
	}
        if (next.done) return null;
    }
    return { txt: res,
	     span: next.value[1],
	     indexStart: indexStart,
	     indexEnd: pos}
}

waiting = [];
processing = null;

function sendNextCommand() {
    let cmd = getNextCommand();
    waiting.push(cmd);
    first_to_push = cmd.indexEnd + 1;
    trySend();
}

function trySend() {
    if (waiting.length > 0 && !processing) {
	const cmd = waiting.shift();
	processing = cmd;
	phox_worker.postMessage(cmd.txt);
    }
}

function goTo(end=false) {
    const el = document.getElementsByClassName('editor')[0]; // assume one editor
    el.focus();
    let index = first_to_push;
    while(true) {
	const cmd = getNextCommand(index, target=end?null:el.caret().span);
	if (!cmd || !cmd.span) break;
	waiting.push(cmd);
	index = cmd.indexEnd + 1
	first_to_push = index;
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
	for (let file of menu.files) {
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
    load_file("tutorial/french/intro_quest.phx");
    restart();
});

document.addEventListener('keydown', e => {
    if (e.ctrlKey && e.code === 'ArrowRight') {
        sendNextCommand();
        e.preventDefault();
    }
    if (e.ctrlKey && e.code === 'ArrowLeft') {
        undo();
        e.preventDefault();
    }
});
