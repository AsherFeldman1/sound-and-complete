// knob.js: turn an <input type="range"> into an amp knob.
// A black skirted knob with 1-10 printed on the skirt; it turns, and you read
// the number under the white mark on the panel. The range input keeps the
// value (and fires "input" events), so the rest of the app is unchanged.
// Drag up/down, scroll, or use the arrow keys.

const SWEEP = 270; // degrees from 1 to 10

/**
 * @param {HTMLInputElement} input  a range input already in the page
 * @param {{numbers?: boolean, sweep?: number}} [o]  numbers: print 1-10 on the
 *   skirt (amp knob); without, a plain knurled pedal knob with a pointer line.
 */
export function makeKnob(input, { numbers = true, sweep = SWEEP } = {}) {
  const min = Number(input.min), max = Number(input.max), step = Number(input.step) || 1;
  const knob = document.createElement("div");
  knob.className = numbers ? "knob" : "knob plain";
  knob.tabIndex = 0;
  knob.setAttribute("role", "slider");
  knob.setAttribute("aria-label", input.getAttribute("aria-label") || "");
  knob.setAttribute("aria-valuemin", min);
  knob.setAttribute("aria-valuemax", max);
  const body = document.createElement("div");
  body.className = "knob-body";
  for (let n = 1; numbers && n <= 10; n++) {
    const s = document.createElement("span");
    const a = -SWEEP / 2 + (n - 1) * (SWEEP / 9);
    s.style.transform = `rotate(${a}deg)`;
    s.textContent = n;
    body.append(s);
  }
  const cap = document.createElement("i");
  body.append(cap);
  knob.append(body);
  input.classList.add("knob-input");
  input.tabIndex = -1;
  input.before(knob);

  const render = () => {
    const f = (Number(input.value) - min) / (max - min);
    // Amp knob: the skirt turns under a fixed mark. Pedal knob: the pointer turns.
    body.style.transform = numbers ? `rotate(${SWEEP / 2 - SWEEP * f}deg)` : `rotate(${-sweep / 2 + sweep * f}deg)`;
    knob.setAttribute("aria-valuenow", input.value);
  };
  const set = (v) => {
    v = Math.min(max, Math.max(min, Math.round(v / step) * step));
    if (v !== Number(input.value)) {
      input.value = v;
      input.dispatchEvent(new Event("input", { bubbles: true }));
    }
    render();
  };

  knob.addEventListener("pointerdown", (e) => {
    e.preventDefault();
    knob.focus();
    knob.setPointerCapture(e.pointerId);
    const y0 = e.clientY, v0 = Number(input.value);
    const move = (m) => set(v0 + ((y0 - m.clientY) / 160) * (max - min));
    const up = () => { knob.removeEventListener("pointermove", move); knob.removeEventListener("pointerup", up); };
    knob.addEventListener("pointermove", move);
    knob.addEventListener("pointerup", up);
  });
  knob.addEventListener("wheel", (e) => {
    e.preventDefault();
    set(Number(input.value) - Math.sign(e.deltaY) * Math.max(step, (max - min) / 50));
  }, { passive: false });
  knob.addEventListener("keydown", (e) => {
    const big = (max - min) / 10;
    const d = { ArrowUp: step, ArrowRight: step, ArrowDown: -step, ArrowLeft: -step, PageUp: big, PageDown: -big }[e.key];
    if (e.key === "Home") set(min);
    else if (e.key === "End") set(max);
    else if (d === undefined) return;
    else set(Number(input.value) + d);
    e.preventDefault();
  });
  input.addEventListener("input", render);
  render();
  return { render };
}
