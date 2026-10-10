from __future__ import annotations

import os
import re
import sys
import shlex
import ctypes
import asyncio
import logging
import plistlib
import tkinter as tk
from pathlib import Path
from collections import abc
from textwrap import dedent
from dataclasses import dataclass
from tkinter.font import Font
from contextlib import suppress
from functools import partial, cached_property
from datetime import datetime, timedelta, timezone
from tkinter import ttk, StringVar, DoubleVar, IntVar
from typing import Any, Union, Tuple, TypedDict, NoReturn, Generic, TYPE_CHECKING

import pystray
import customtkinter as ctk
from yarl import URL
from PIL.ImageTk import PhotoImage
from PIL import Image as Image_module, ImageDraw

if sys.platform == "win32":
    import win32api
    import win32con
    import win32gui

if sys.platform == "darwin":
    import AppKit

from translate import _
from cache import ImageCache
from exceptions import MinerException, ExitRequest
from utils import resource_path, set_root_icon, webopen, task_wrapper, Game, _T
from constants import (
    MAX_INT,
    URLType,
    SELF_PATH,
    IS_PACKAGED,
    SCRIPTS_PATH,
    WINDOW_TITLE,
    LOGGING_LEVELS,
    MAX_WEBSOCKETS,
    WS_TOPICS_LIMIT,
    OUTPUT_FORMATTER,
    State,
    PriorityMode,
)
if sys.platform == "win32":
    from registry import RegistryKey, ValueType, ValueNotFound


if TYPE_CHECKING:
    from twitch import Twitch
    from channel import Channel
    from settings import Settings
    from inventory import DropsCampaign, TimedDrop
    from PIL.Image import Image


logger = logging.getLogger("TwitchDrops")
TK_PADDING = Union[int, Tuple[int, int], Tuple[int, int, int], Tuple[int, int, int, int]]

# (light, dark) color pairs used by every CustomTkinter widget in the app.
# CustomTkinter widgets re-paint themselves automatically on ctk.set_appearance_mode(...)
# as long as they were constructed with a (light, dark) tuple, so this is the single
# source of truth for the palette - no manual per-widget recoloring is needed on toggle.
PALETTE: dict[str, tuple[str, str]] = {
    "bg": ("#f7f8fa", "#1e1e1e"),
    "surface": ("#ffffff", "#252525"),
    "border": ("#e4e7ec", "#3c3c3c"),
    "fg": ("#1a1d23", "#e6e6e6"),
    "muted": ("#6b7280", "#b3b3b3"),
    "link": ("#5b21b6", "#4ea3ff"),
    "accent": ("#5b21b6", "#0d99ff"),
    "accent_hover": ("#4c1d95", "#3fb0ff"),
    "on_accent": ("#ffffff", "#ffffff"),
    "ok": ("#12b76a", "#3ddc84"),
    "warn": ("#dc6803", "#e8b339"),
    "danger": ("#f04438", "#ff6b61"),
    "sel": ("#ede6ff", "#094771"),
    "accent_soft": ("#c4b5fd", "#2a3a66"),  # lighter secondary progress-bar fill
    "ok_soft": ("#e7f8ee", "#103324"),  # "live" badge background
}


######################
# GUI ELEMENTS START #
######################


class _TKOutputHandler(logging.Handler):
    def __init__(self, output: GUIManager):
        super().__init__()
        self._output = output

    def emit(self, record):
        self._output.print(self.format(record))


class PlaceholderEntry(ctk.CTkEntry):
    """
    CTkEntry already supports placeholder text/color natively (including the
    .get() returning '' while the placeholder is showing), so this is now just
    a thin wrapper adding the .clear()/.replace() convenience methods the rest
    of the app expects.
    """
    def __init__(self, master: Any, *args: Any, placeholder: str, prefill: str = '', **kwargs: Any):
        kwargs.setdefault("placeholder_text", placeholder)
        kwargs.setdefault("placeholder_text_color", PALETTE["muted"])
        kwargs.setdefault("fg_color", PALETTE["surface"])
        kwargs.setdefault("text_color", PALETTE["fg"])
        kwargs.setdefault("border_color", PALETTE["border"])
        super().__init__(master, *args, **kwargs)
        if prefill:
            self.insert(0, prefill)

    def clear(self) -> None:
        self.delete(0, "end")

    def replace(self, content: str) -> None:
        self.delete(0, "end")
        self.insert(0, content)


class PlaceholderComboBox(ctk.CTkComboBox):
    """
    CTkComboBox has no native placeholder support (unlike CTkEntry), so this
    implements the same show-grey-text-until-focused behavior by hand, directly
    on the plain tkinter.Entry it keeps internally as `._entry`.
    """
    _PLACEHOLDER_COLOR = "grey60"

    def __init__(self, master: Any, *args: Any, placeholder: str, **kwargs: Any):
        kwargs.setdefault("fg_color", PALETTE["surface"])
        kwargs.setdefault("text_color", PALETTE["fg"])
        kwargs.setdefault("border_color", PALETTE["border"])
        kwargs.setdefault("button_color", PALETTE["surface"])
        # CTkComboBox defaults to a single literal "CTkComboBox" entry (both as the
        # text it inserts into the field AND as the dropdown's one selectable option)
        # whenever no 'values' kwarg is given - start it with an empty list instead,
        # so the dropdown doesn't offer that literal string as a choice before the
        # real values (set later via .configure(values=...)) ever arrive.
        kwargs.setdefault("values", [])
        super().__init__(master, *args, **kwargs)
        self._ph_text: str = placeholder
        self._ph: bool = False
        self._entry.delete(0, "end")
        self._entry.bind("<FocusIn>", self._focus_in)
        self._entry.bind("<FocusOut>", self._focus_out)
        self._insert_placeholder()

    def _insert_placeholder(self) -> None:
        if not self._entry.get():
            self._ph = True
            self._entry.configure(fg=self._PLACEHOLDER_COLOR)
            self._entry.insert(0, self._ph_text)

    def _remove_placeholder(self) -> None:
        if self._ph:
            self._ph = False
            self._entry.delete(0, "end")
            self._entry.configure(fg=self._apply_appearance_mode(self._text_color))

    def _focus_in(self, event: tk.Event[Any] | None = None) -> None:
        self._remove_placeholder()

    def _focus_out(self, event: tk.Event[Any] | None = None) -> None:
        self._insert_placeholder()

    def get(self) -> str:
        if self._ph:
            return ''
        return super().get()

    def clear(self) -> None:
        self._remove_placeholder()
        self._entry.delete(0, "end")
        self._insert_placeholder()


class PaddedListbox(tk.Listbox):
    def __init__(self, master: ttk.Widget, *args, padding: TK_PADDING = (0, 0, 0, 0), **kwargs):
        # we place the listbox inside a frame with the same background
        # this means we need to forward the 'grid' method to the frame, not the listbox
        self._frame = tk.Frame(master)
        self._frame.rowconfigure(0, weight=1)
        self._frame.columnconfigure(0, weight=1)
        super().__init__(self._frame)
        # mimic default listbox style with sunken relief and borderwidth of 1
        if "relief" not in kwargs:
            kwargs["relief"] = "sunken"
        if "borderwidth" not in kwargs:
            kwargs["borderwidth"] = 1
        self.configure(*args, padding=padding, **kwargs)

    def grid(self, *args, **kwargs):
        return self._frame.grid(*args, **kwargs)

    def grid_remove(self) -> None:
        return self._frame.grid_remove()

    def grid_info(self) -> tk._GridInfo:
        return self._frame.grid_info()

    def grid_forget(self) -> None:
        return self._frame.grid_forget()

    def configure(self, *args: Any, **kwargs: Any) -> Any:
        options: dict[str, Any] = {}
        if args and args[0] is not None:
            options.update(args[0])
        if kwargs:
            options.update(kwargs)
        # NOTE on processed options:
        # • relief is applied to the frame only
        # • background is copied, so that both listbox and frame change color
        # • borderwidth is applied to the frame only
        # bg is folded into background for easier processing
        if "bg" in options:
            options["background"] = options.pop("bg")
        frame_options = {}
        if "relief" in options:
            frame_options["relief"] = options.pop("relief")
        if "background" in options:
            frame_options["background"] = options["background"]  # copy
        if "borderwidth" in options:
            frame_options["borderwidth"] = options.pop("borderwidth")
        self._frame.configure(frame_options)
        # update padding
        if "padding" in options:
            padding: TK_PADDING = options.pop("padding")
            padx1: tk._ScreenUnits
            padx2: tk._ScreenUnits
            pady1: tk._ScreenUnits
            pady2: tk._ScreenUnits
            if not isinstance(padding, tuple) or len(padding) == 1:
                if isinstance(padding, tuple):
                    padding = padding[0]
                padx1 = padx2 = pady1 = pady2 = padding
            elif len(padding) == 2:
                padx1 = padx2 = padding[0]
                pady1 = pady2 = padding[1]
            elif len(padding) == 3:
                padx1, padx2 = padding[0], padding[1]
                pady1 = pady2 = padding[2]
            else:
                padx1, padx2, pady1, pady2 = padding
            super().grid(column=0, row=0, padx=(padx1, padx2), pady=(pady1, pady2), sticky="nsew")
        else:
            super().grid(column=0, row=0, sticky="nsew")
        # listbox uses flat relief to blend in with the inside of the frame
        options["relief"] = "flat"
        return super().configure(options)

    def config(self, *args: Any, **kwargs: Any) -> Any:
        # because 'config = configure' makes mypy complain
        self.configure(*args, **kwargs)

    def configure_theme(self, *, bg: str, fg: str, sel_bg: str, sel_fg: str):
        # Apply basic colors for dark/light mode
        super().configure(bg=bg, fg=fg, selectbackground=sel_bg, selectforeground=sel_fg)


class MouseOverLabel(ctk.CTkLabel):
    def __init__(self, *args, alt_text: str = '', reverse: bool = False, **kwargs) -> None:
        self._org_text: str = ''
        self._alt_text: str = ''
        self._alt_reverse: bool = reverse
        self._bind_enter: str | None = None
        self._bind_leave: str | None = None
        super().__init__(*args, **kwargs)
        self.configure(text=kwargs.get("text", ''), alt_text=alt_text, reverse=reverse)

    def _set_org(self, event: tk.Event[MouseOverLabel]):
        super().configure(text=self._org_text)

    def _set_alt(self, event: tk.Event[MouseOverLabel]):
        super().configure(text=self._alt_text)

    def configure(self, *args: Any, **kwargs: Any) -> Any:
        options: dict[str, Any] = {}
        if args and args[0] is not None:
            options.update(args[0])
        if kwargs:
            options.update(kwargs)
        applicable_options: set[str] = set((
            "text",
            "reverse",
            "alt_text",
        ))
        if applicable_options.intersection(options.keys()):
            # we need to pop some options, because they can't be passed down to the label,
            # as that will result in an error later down the line
            events_change: bool = False
            if "text" in options:
                if bool(self._org_text) != bool(options["text"]):
                    events_change = True
                self._org_text = options["text"]
            if "alt_text" in options:
                if bool(self._alt_text) != bool(options["alt_text"]):
                    events_change = True
                self._alt_text = options.pop("alt_text")
            if "reverse" in options:
                if bool(self._alt_reverse) != bool(options["reverse"]):
                    events_change = True
                self._alt_reverse = options.pop("reverse")
            if self._org_text and not self._alt_text:
                options["text"] = self._org_text
            elif (not self._org_text or self._alt_reverse) and self._alt_text:
                options["text"] = self._alt_text
            if events_change:
                if self._bind_enter is not None:
                    self.unbind(self._bind_enter)
                    self._bind_enter = None
                if self._bind_leave is not None:
                    self.unbind(self._bind_leave)
                    self._bind_leave = None
                if self._org_text and self._alt_text:
                    if self._alt_reverse:
                        self._bind_enter = self.bind("<Enter>", self._set_org)
                        self._bind_leave = self.bind("<Leave>", self._set_alt)
                    else:
                        self._bind_enter = self.bind("<Enter>", self._set_alt)
                        self._bind_leave = self.bind("<Leave>", self._set_org)
        return super().configure(**options)

    def config(self, *args: Any, **kwargs: Any) -> Any:
        # because 'config = configure' makes mypy complain
        self.configure(*args, **kwargs)


class LinkLabel(ctk.CTkLabel):
    _FONT: ctk.CTkFont | None = None

    def __init__(self, *args, link: str, plain: bool = False, **kwargs) -> None:
        self._link: str = link
        if not plain:
            if "text_color" not in kwargs:
                kwargs["text_color"] = PALETTE["link"]
            if "font" not in kwargs:
                if LinkLabel._FONT is None:
                    LinkLabel._FONT = ctk.CTkFont(underline=True)
                kwargs["font"] = LinkLabel._FONT
            if "cursor" not in kwargs:
                kwargs["cursor"] = "hand2"
        super().__init__(*args, **kwargs)
        self.bind("<ButtonRelease-1>", lambda e: webopen(self._link))


class SelectMenu(tk.Menubutton, Generic[_T]):
    def __init__(
        self,
        master: tk.Misc,
        *args: Any,
        tearoff: bool = False,
        options: dict[str, _T],
        command: abc.Callable[[_T], Any] | None = None,
        default: str | None = None,
        relief: tk._Relief = "solid",
        background: str = "white",
        **kwargs: Any,
    ):
        width = max((len(k) for k in options.keys()), default=20)
        super().__init__(
            master, *args, background=background, relief=relief, width=width, **kwargs
        )
        self._menu_options: dict[str, _T] = options
        self._command = command
        self.menu = tk.Menu(self, tearoff=tearoff)
        self.configure(menu=self.menu)
        for name in options.keys():
            self.menu.add_command(label=name, command=partial(self._select, name))
        if default is not None and default in self._menu_options:
            self.configure(text=default)

    def _select(self, option: str) -> None:
        self.configure(text=option)
        if self._command is not None:
            self._command(self._menu_options[option])

    def get(self) -> _T:
        return self._menu_options[self.cget("text")]


class SelectCombobox(ctk.CTkOptionMenu):
    """
    A read-only, fixed-choice dropdown (Language / Priority mode selectors).
    Named/shaped like the old ttk.Combobox-based version so call sites don't
    need to change: 'command' is still invoked as command(event), with event
    always None, since none of the existing callbacks use it.
    """
    def __init__(
        self,
        master: tk.Misc,
        *args,
        width_offset: int = 0,
        width: int | None = None,
        textvariable: tk.StringVar,
        values: list[str] | tuple[str, ...],
        command: abc.Callable[[tk.Event[Any] | None], None] | None = None,
        **kwargs,
    ) -> None:
        if width is None:
            font = Font(master, size=13)
            width = max((font.measure(v) for v in values), default=100) + 48
        width += width_offset
        self._user_command = command
        super().__init__(
            master,
            *args,
            width=width,
            values=list(values),
            variable=textvariable,
            command=self._on_select,
            fg_color=PALETTE["surface"],
            text_color=PALETTE["fg"],
            button_color=PALETTE["surface"],
            button_hover_color=PALETTE["border"],
            dropdown_fg_color=PALETTE["surface"],
            dropdown_text_color=PALETTE["fg"],
            dropdown_hover_color=PALETTE["sel"],
            **kwargs,
        )

    def _on_select(self, value: str) -> None:
        if self._user_command is not None:
            self._user_command(None)


###########################################
# GUI ELEMENTS END / GUI DEFINITION START #
###########################################


def make_card(
    master: tk.Misc, title: str | None, *, corner_radius: int = 14, small: bool = False
) -> tuple[ctk.CTkFrame, ctk.CTkFrame]:
    """
    Builds a titled "card": a rounded, bordered frame with a title pinned at
    its top, mimicking the look of the old ttk.LabelFrame sections.
    Returns (outer, inner) - grid the outer into the parent layout, then grid
    content into the returned inner frame exactly like the old LabelFrame body.

    title=None skips the title row entirely (content starts flush at the top,
    e.g. the Account card). small=True renders it as a tiny muted uppercase
    eyebrow (e.g. "CONNECTION"/"ACTIVITY") instead of the normal bold title
    used by most cards (e.g. "Channels").
    """
    outer = ctk.CTkFrame(
        master,
        corner_radius=corner_radius,
        fg_color=PALETTE["surface"],
        border_width=1,
        border_color=PALETTE["border"],
    )
    outer.grid_columnconfigure(0, weight=1)
    content_row = 0
    if title:
        if small:
            ctk.CTkLabel(
                outer,
                text=title.upper(),
                font=ctk.CTkFont(size=11, weight="bold"),
                text_color=PALETTE["muted"],
                anchor="w",
            ).grid(column=0, row=0, sticky="w", padx=14, pady=(12, 2))
        else:
            ctk.CTkLabel(
                outer,
                text=title,
                font=ctk.CTkFont(weight="bold"),
                text_color=PALETTE["fg"],
                anchor="w",
            ).grid(column=0, row=0, sticky="w", padx=14, pady=(10, 2))
        content_row = 1
    inner = ctk.CTkFrame(outer, fg_color="transparent")
    inner.grid(column=0, row=content_row, sticky="nsew", padx=10, pady=(0 if title else 10, 10))
    outer.grid_rowconfigure(content_row, weight=1)
    return outer, inner


def make_separator(master: tk.Misc) -> ctk.CTkFrame:
    return ctk.CTkFrame(master, height=1, fg_color=PALETTE["border"])


_circle_icon_cache: dict[tuple[int, str], PhotoImage] = {}


def circle_icon(size: int, color: str) -> PhotoImage:
    """A plain solid-color circle, used as a decorative placeholder (e.g. in place
    of a per-channel avatar, which Twitch's API/this app has no image for)."""
    key = (size, color)
    if key not in _circle_icon_cache:
        img = Image_module.new("RGBA", (size, size), (0, 0, 0, 0))
        ImageDraw.Draw(img).ellipse((0, 0, size - 1, size - 1), fill=color)
        _circle_icon_cache[key] = PhotoImage(img)
    return _circle_icon_cache[key]


class StatusBar:
    """
    Renders as a small pill badge mounted into CampaignProgress's badge_slot
    (top-right of the "now mining" hero card), rather than its own boxed
    section - there's no separate "Status" card in the redesigned layout.
    """
    # prefix of the translated "Watching: {channel}" status text, used to detect
    # the one status that means "actively mining" and deserves the green "live"
    # treatment, as opposed to idle/transitional states
    _WATCHING_PREFIX = _("status", "watching").split("{")[0]

    def __init__(self, manager: GUIManager, master: tk.Misc):
        self._badge = badge = ctk.CTkFrame(master, corner_radius=999, fg_color=PALETTE["sel"])
        badge.grid(column=0, row=0, sticky="e")
        self._dot = ctk.CTkFrame(
            badge, width=6, height=6, corner_radius=3, fg_color=PALETTE["accent"],
        )
        self._dot.grid(column=0, row=0, padx=(10, 6), pady=6)
        self._label = ctk.CTkLabel(
            badge,
            text='',
            text_color=PALETTE["accent"],
            font=ctk.CTkFont(size=11, weight="bold"),
        )
        self._label.grid(column=1, row=0, padx=(0, 10), pady=6)

    def update(self, text: str):
        self._label.configure(text=text.upper())
        live = text.startswith(self._WATCHING_PREFIX)
        color = PALETTE["ok"] if live else PALETTE["accent"]
        self._badge.configure(fg_color=PALETTE["ok_soft"] if live else PALETTE["sel"])
        self._dot.configure(fg_color=color)
        self._label.configure(text_color=color)

    def clear(self):
        self._label.configure(text='')


class _WSEntry(TypedDict):
    status: str
    topics: int


class WebsocketStatus:
    """
    "Connection" card: an aggregate "N/MAX connected" readout plus one small
    colored bar segment per websocket (green once connected), rather than the
    old raw per-socket status/topic-count text dump. The per-socket detail is
    still tracked internally (and summed into the topic count) - it's just not
    spelled out status-by-status in the UI anymore.
    """
    def __init__(self, manager: GUIManager, master: tk.Misc):
        frame, body = make_card(master, "CONNECTION", small=True)
        frame.grid(column=0, row=1, sticky="nsew", pady=(0, 10))
        body.columnconfigure(0, weight=1)
        self._connected_text = StringVar(body)
        self._topics_text = StringVar(body)
        ctk.CTkLabel(
            body,
            textvariable=self._connected_text,
            font=ctk.CTkFont(size=15, weight="bold"),
            text_color=PALETTE["fg"],
            anchor="w",
        ).grid(column=0, row=0, sticky="w")
        ctk.CTkLabel(
            body, textvariable=self._topics_text, text_color=PALETTE["muted"], anchor="w",
        ).grid(column=0, row=1, sticky="w", pady=(0, 10))
        bars_row = ctk.CTkFrame(body, fg_color="transparent")
        bars_row.grid(column=0, row=2, sticky="ew")
        self._bars: list[ctk.CTkFrame] = []
        for i in range(MAX_WEBSOCKETS):
            bars_row.columnconfigure(i, weight=1)
            bar = ctk.CTkFrame(
                bars_row, height=5, corner_radius=3, fg_color=PALETTE["border"]
            )
            bar.grid(column=i, row=0, sticky="ew", padx=(0 if i == 0 else 4, 0))
            self._bars.append(bar)
        self._items: dict[int, _WSEntry | None] = {i: None for i in range(MAX_WEBSOCKETS)}
        self._update()

    def update(self, idx: int, status: str | None = None, topics: int | None = None):
        if status is None and topics is None:
            raise TypeError("You need to provide at least one of: status, topics")
        entry = self._items.get(idx)
        if entry is None:
            entry = self._items[idx] = _WSEntry(
                status=_("gui", "websocket", "disconnected"), topics=0
            )
        if status is not None:
            entry["status"] = status
        if topics is not None:
            entry["topics"] = topics
        self._update()

    def remove(self, idx: int):
        if idx in self._items:
            del self._items[idx]
            self._update()

    def _update(self):
        connected_label = _("gui", "websocket", "connected")
        connected = 0
        total_topics = 0
        for idx in range(MAX_WEBSOCKETS):
            item = self._items.get(idx)
            is_connected = item is not None and item["status"] == connected_label
            self._bars[idx].configure(
                fg_color=PALETTE["ok"] if is_connected else PALETTE["border"]
            )
            if is_connected:
                connected += 1
                total_topics += item["topics"]
        self._connected_text.set(f"{connected}/{MAX_WEBSOCKETS} {connected_label.lower()}")
        self._topics_text.set(f"{total_topics}/{MAX_WEBSOCKETS * WS_TOPICS_LIMIT} topics")


@dataclass
class LoginData:
    username: str
    password: str
    token: str


class LoginForm:
    """
    Renders as the "Account" card (avatar circle + status + user id). The main
    button doubles as Login (device-code flow) while logged out, and as Logout
    (token invalidation) while logged in - toggled in update().
    """
    def __init__(self, manager: GUIManager, master: tk.Misc):
        self._manager = manager
        self._status_text = StringVar(master)
        self._id_text = StringVar(master)
        frame, body = make_card(master, None)
        frame.grid(column=0, row=0, sticky="nsew", pady=(0, 10))
        body.columnconfigure(1, weight=1)

        ctk.CTkLabel(
            body, text='', width=36, height=36, corner_radius=18, fg_color=PALETTE["sel"],
        ).grid(column=0, row=0, rowspan=2, padx=(0, 10))
        status_row = ctk.CTkFrame(body, fg_color="transparent")
        status_row.grid(column=1, row=0, sticky="w")
        self._status_dot = ctk.CTkFrame(
            status_row, width=8, height=8, corner_radius=4, fg_color=PALETTE["muted"],
        )
        self._status_dot.grid(column=0, row=0, padx=(0, 6))
        ctk.CTkLabel(
            status_row,
            textvariable=self._status_text,
            font=ctk.CTkFont(weight="bold"),
            text_color=PALETTE["fg"],
            anchor="w",
        ).grid(column=1, row=0, sticky="w")
        ctk.CTkLabel(
            body, textvariable=self._id_text, text_color=PALETTE["muted"], anchor="w",
        ).grid(column=1, row=1, sticky="w")

        self._login_entry = PlaceholderEntry(body, placeholder=_("gui", "login", "username"))
        # self._login_entry.grid(column=0, row=2, columnspan=2)
        self._pass_entry = PlaceholderEntry(
            body, placeholder=_("gui", "login", "password"), show='•'
        )
        # self._pass_entry.grid(column=0, row=3, columnspan=2)
        self._token_entry = PlaceholderEntry(body, placeholder=_("gui", "login", "twofa_code"))
        # self._token_entry.grid(column=0, row=4, columnspan=2)

        self._confirm = asyncio.Event()
        self._button = ctk.CTkButton(
            body,
            text=_("gui", "login", "button"),
            command=self._confirm.set,
            state="disabled",
            font=ctk.CTkFont(weight="bold"),
            fg_color=PALETTE["accent"],
            hover_color=PALETTE["accent_hover"],
            text_color=PALETTE["on_accent"],
        )
        self._button.grid(column=0, row=5, columnspan=2, sticky="ew", pady=(10, 0))
        self.update(_("gui", "login", "logged_out"), None)

    def clear(self, login: bool = False, password: bool = False, token: bool = False):
        clear_all = not login and not password and not token
        if login or clear_all:
            self._login_entry.clear()
        if password or clear_all:
            self._pass_entry.clear()
        if token or clear_all:
            self._token_entry.clear()

    async def wait_for_login_press(self) -> None:
        self._confirm.clear()
        try:
            self._button.configure(state="normal")
            await self._manager.coro_unless_closed(self._confirm.wait())
        finally:
            self._button.configure(state="disabled")

    async def ask_login(self) -> LoginData:
        self.update(_("gui", "login", "required"), None)
        # ensure the window isn't hidden into tray when this runs
        self._manager.grab_attention(sound=False)
        while True:
            self._manager.print(_("gui", "login", "request"))
            await self.wait_for_login_press()
            login_data = LoginData(
                self._login_entry.get().strip(),
                self._pass_entry.get(),
                self._token_entry.get().strip(),
            )
            # basic input data validation: 3-25 characters in length, only ascii and underscores
            if (
                not 3 <= len(login_data.username) <= 25
                and re.match(r'^[a-zA-Z0-9_]+$', login_data.username)
            ):
                self.clear(login=True)
                continue
            if len(login_data.password) < 8:
                self.clear(password=True)
                continue
            if login_data.token and len(login_data.token) < 6:
                self.clear(token=True)
                continue
            return login_data

    async def ask_enter_code(self, page_url: URL, user_code: str) -> None:
        self.update(_("gui", "login", "required"), None)
        # ensure the window isn't hidden into tray when this runs
        self._manager.grab_attention(sound=False)
        self._manager.print(_("gui", "login", "request"))
        await self.wait_for_login_press()
        self._manager.print(f"Enter this code on the Twitch's device activation page: {user_code}")
        await asyncio.sleep(4)
        webopen(page_url)

    def update(self, status: str, user_id: int | None):
        user_str = str(user_id) if user_id is not None else "-"
        self._status_text.set(status)
        self._id_text.set(f"ID {user_str}")
        logged_in = status == _("gui", "login", "logged_in")
        if logged_in:
            dot_color = PALETTE["ok"]
        elif status == _("gui", "login", "logged_out"):
            dot_color = PALETTE["muted"]
        else:
            dot_color = PALETTE["warn"]
        self._status_dot.configure(fg_color=dot_color)
        if logged_in:
            # repurpose the button as a logout action while we're logged in,
            # instead of a separate "Invalidate" link
            self._button.configure(
                text=_("gui", "login", "logout_button"),
                state="normal",
                command=lambda: self._manager.help.invalidate_token(),
            )
        else:
            self._button.configure(
                text=_("gui", "login", "button"),
                state="disabled",
                command=self._confirm.set,
            )


class _BaseVars(TypedDict):
    progress: DoubleVar
    percentage: StringVar
    remaining: StringVar


class _CampaignVars(_BaseVars):
    name: StringVar
    game: StringVar


class _DropVars(_BaseVars):
    rewards: StringVar


class _ProgressVars(TypedDict):
    campaign: _CampaignVars
    drop: _DropVars


class CampaignProgress:
    def __init__(self, manager: GUIManager, master: tk.Misc):
        self._manager = manager
        self._vars: _ProgressVars = {
            "campaign": {
                "name": StringVar(master),  # campaign name
                "game": StringVar(master),  # game name
                "progress": DoubleVar(master),  # controls the progress bar
                "percentage": StringVar(master),  # percentage display string
                "remaining": StringVar(master),  # time remaining string, filled via _update_time
            },
            "drop": {
                "rewards": StringVar(master),  # drop rewards
                "progress": DoubleVar(master),  # as above
                "percentage": StringVar(master),  # as above
                "remaining": StringVar(master),  # as above
            },
        }
        # "Now mining" hero card: icon + game/campaign title (+ a badge slot that
        # StatusBar fills in) up top, the drop and campaign progress bars below.
        outer = ctk.CTkFrame(
            master,
            corner_radius=16,
            fg_color=PALETTE["surface"],
            border_width=1,
            border_color=PALETTE["border"],
        )
        self._frame = outer
        outer.grid(column=0, row=0, sticky="nsew", pady=(0, 10))
        outer.columnconfigure(1, weight=1)

        self._icon_label = ctk.CTkLabel(
            outer,
            text="⛏",
            width=150,
            height=144,
            # 0, not rounded - CTkLabel insets its content by min(corner_radius, height/2)
            # on each side to keep text clear of rounded corners, which would otherwise
            # leave the fg_color background showing around a full-bleed box art image.
            corner_radius=0,
            fg_color=PALETTE["accent"],
            text_color=PALETTE["on_accent"],
            font=ctk.CTkFont(size=28, weight="bold"),
        )
        # sticky="nsew" - stretches to the full card height (header + body rows);
        # _render_icon() re-crops/re-renders the box art to match on every resize,
        # so the fixed-size image doesn't end up smaller than the stretched label.
        self._icon_label.grid(column=0, row=0, rowspan=2, sticky="nsew", padx=18, pady=18)
        self._icon_label.bind("<Configure>", self._on_icon_configure)

        header = ctk.CTkFrame(outer, fg_color="transparent")
        header.grid(column=1, row=0, sticky="nsew", pady=(18, 0), padx=(0, 18))
        header.columnconfigure(0, weight=1)
        title_box = ctk.CTkFrame(header, fg_color="transparent")
        title_box.grid(column=0, row=0, sticky="w")
        ctk.CTkLabel(
            title_box,
            text="NOW MINING",
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color=PALETTE["accent"],
            anchor="w",
        ).grid(sticky="w")
        ctk.CTkLabel(
            title_box,
            textvariable=self._vars["campaign"]["game"],
            font=ctk.CTkFont(size=19, weight="bold"),
            text_color=PALETTE["fg"],
            anchor="w",
        ).grid(sticky="w")
        ctk.CTkLabel(
            title_box,
            textvariable=self._vars["campaign"]["name"],
            text_color=PALETTE["muted"],
            anchor="w",
        ).grid(sticky="w")
        # StatusBar mounts its pill/badge into this slot - keeps the two classes
        # independent while still sharing one visual card.
        self.badge_slot = ctk.CTkFrame(header, fg_color="transparent")
        self.badge_slot.grid(column=1, row=0, sticky="ne")

        body = ctk.CTkFrame(outer, fg_color="transparent")
        body.grid(column=1, row=1, sticky="nsew", padx=(0, 18), pady=(10, 18))
        body.columnconfigure(0, weight=1)

        drop_row = ctk.CTkFrame(body, fg_color="transparent")
        drop_row.grid(column=0, row=0, sticky="ew")
        drop_row.columnconfigure(0, weight=1)
        ctk.CTkLabel(
            drop_row,
            textvariable=self._vars["drop"]["rewards"],
            font=ctk.CTkFont(weight="bold"),
            text_color=PALETTE["fg"],
            anchor="w",
        ).grid(column=0, row=0, sticky="w")
        ctk.CTkLabel(
            drop_row, textvariable=self._vars["drop"]["remaining"], text_color=PALETTE["muted"],
        ).grid(column=1, row=0, sticky="e")
        ctk.CTkProgressBar(
            body,
            height=8,
            corner_radius=4,
            fg_color=PALETTE["border"],
            progress_color=PALETTE["accent"],
            variable=self._vars["drop"]["progress"],
        ).grid(column=0, row=1, sticky="ew", pady=(6, 14))

        campaign_row = ctk.CTkFrame(body, fg_color="transparent")
        campaign_row.grid(column=0, row=2, sticky="ew")
        campaign_row.columnconfigure(0, weight=1)
        ctk.CTkLabel(
            campaign_row,
            text=_("gui", "progress", "campaign_progress"),
            text_color=PALETTE["muted"],
            anchor="w",
        ).grid(column=0, row=0, sticky="w")
        ctk.CTkLabel(
            campaign_row, textvariable=self._vars["campaign"]["percentage"],
            text_color=PALETTE["muted"],
        ).grid(column=1, row=0, sticky="e")
        ctk.CTkProgressBar(
            body,
            height=6,
            corner_radius=3,
            fg_color=PALETTE["border"],
            progress_color=PALETTE["accent_soft"],
            variable=self._vars["campaign"]["progress"],
        ).grid(column=0, row=3, sticky="ew", pady=(6, 2))

        self._drop: TimedDrop | None = None
        self._seconds: int = 0
        self._timer_task: asyncio.Task[None] | None = None
        self._icon_url: URLType | None = None
        self._icon_task: asyncio.Task[None] | None = None
        self._icon_source: Image | None = None
        self._icon_rendered_size: tuple[int, int] = (0, 0)
        self.display(None)

    def _set_icon(self, image_url: URLType) -> None:
        if image_url == self._icon_url:
            return
        self._icon_url = image_url
        if self._icon_task is not None:
            self._icon_task.cancel()

        async def load() -> None:
            self._icon_source = await self._manager._cache.get_image(image_url)
            self._icon_rendered_size = (0, 0)  # force a re-render at the current label size
            self._render_icon()
            self._icon_task = None

        self._icon_task = asyncio.create_task(load())

    def _render_icon(self) -> None:
        source = self._icon_source
        if source is None:
            return
        width = self._icon_label.winfo_width()
        height = self._icon_label.winfo_height()
        if width < 10 or height < 10:
            # not laid out yet (e.g. still starting up) - render at the label's own
            # declared minimum size instead, _on_icon_configure will re-render later
            width, height = 150, 144
        if (width, height) == self._icon_rendered_size:
            return
        self._icon_rendered_size = (width, height)
        # crop to the label's exact aspect ratio first - letting CTkImage's own resize
        # stretch/squish a differently-shaped source would distort the box art
        src_width, src_height = source.size
        target_ratio = width / height
        if src_width / src_height > target_ratio:
            new_width = round(src_height * target_ratio)
            left = (src_width - new_width) // 2
            cropped = source.crop((left, 0, left + new_width, src_height))
        else:
            new_height = round(src_width / target_ratio)
            top = (src_height - new_height) // 2
            cropped = source.crop((0, top, src_width, top + new_height))
        cropped = cropped.resize((width, height), Image_module.Resampling.LANCZOS)
        # CTkLabel can't clip an image to its own rounded corners (corner_radius only
        # rounds its plain background rect) - bake rounded corners into the image data
        # itself instead, filled with the current theme's surface color so they blend
        # into the card background behind it.
        mode_idx = 1 if ctk.get_appearance_mode() == "Dark" else 0
        bg_color = PALETTE["surface"][mode_idx]
        mask = Image_module.new("L", (width, height), 0)
        ImageDraw.Draw(mask).rounded_rectangle((0, 0, width - 1, height - 1), radius=14, fill=255)
        rounded = Image_module.new("RGB", (width, height), bg_color)
        rounded.paste(cropped.convert("RGB"), mask=mask)
        icon = ctk.CTkImage(light_image=rounded, size=(width, height))
        # can fire (via the <Configure> binding) after the window has started tearing
        # down on exit, by which point the widget's underlying Tcl image is already gone
        with suppress(tk.TclError):
            self._icon_label.configure(image=icon, text="")

    def _on_icon_configure(self, event: tk.Event) -> None:
        self._render_icon()

    def _clear_icon(self) -> None:
        self._icon_url = None
        self._icon_source = None
        if self._icon_task is not None:
            self._icon_task.cancel()
            self._icon_task = None
        # can run during shutdown (clear_drop -> display(None)), after the previous
        # CTkImage's underlying Tcl image has already been torn down
        with suppress(tk.TclError):
            self._icon_label.configure(image=None, text="⛏")

    def _divmod(self, minutes: int) -> tuple[int, int]:
        if self._seconds < 60 and minutes > 0:
            minutes -= 1
        hours, minutes = divmod(minutes, 60)
        return (hours, minutes)

    def _update_time(self, seconds: int | None = None):
        if seconds is not None:
            self._seconds = seconds
        drop = self._drop
        if drop is not None:
            drop_minutes = drop.remaining_minutes
            campaign_minutes = drop.campaign.remaining_minutes
        else:
            drop_minutes = 0
            campaign_minutes = 0
        drop_vars: _DropVars = self._vars["drop"]
        campaign_vars: _CampaignVars = self._vars["campaign"]
        dseconds = self._seconds % 60
        hours, minutes = self._divmod(drop_minutes)
        drop_vars["remaining"].set(
            _("gui", "progress", "remaining").format(time=f"{hours:>2}:{minutes:02}:{dseconds:02}")
        )
        hours, minutes = self._divmod(campaign_minutes)
        campaign_vars["remaining"].set(
            _("gui", "progress", "remaining").format(time=f"{hours:>2}:{minutes:02}:{dseconds:02}")
        )

    async def _timer_loop(self):
        self._update_time(60)
        while self._seconds > 0:
            await asyncio.sleep(1)
            self._seconds -= 1
            self._update_time()
        self._timer_task = None

    def start_timer(self):
        if self._timer_task is None:
            if self._drop is None or self._drop.remaining_minutes <= 0:
                # if we're starting the timer at 0 drop minutes,
                # all we need is a single instant time update setting seconds to 60,
                # to avoid substracting a minute from campaign minutes
                self._update_time(60)
            else:
                self._timer_task = asyncio.create_task(self._timer_loop())

    def stop_timer(self):
        if self._timer_task is not None:
            self._timer_task.cancel()
            self._timer_task = None

    def display(self, drop: TimedDrop | None, *, countdown: bool = True, subone: bool = False):
        self._drop = drop
        vars_drop = self._vars["drop"]
        vars_campaign = self._vars["campaign"]
        self.stop_timer()
        if drop is None:
            # clear the drop display
            vars_drop["rewards"].set("...")
            vars_drop["progress"].set(0.0)
            vars_drop["percentage"].set("-%")
            vars_campaign["name"].set("...")
            vars_campaign["game"].set("...")
            vars_campaign["progress"].set(0.0)
            vars_campaign["percentage"].set("-%")
            self._clear_icon()
            self._update_time(0)
            return
        vars_drop["rewards"].set(f"{_('gui', 'progress', 'drop')} {drop.rewards_text()}")
        vars_drop["progress"].set(drop.progress)
        vars_drop["percentage"].set(f"{drop.progress:6.1%}")
        campaign = drop.campaign
        vars_campaign["name"].set(campaign.name)
        vars_campaign["game"].set(campaign.game.name)
        self._set_icon(campaign.image_url)
        vars_campaign["progress"].set(campaign.progress)
        vars_campaign["percentage"].set(f"{campaign.progress:.0%}")
        if countdown:
            # restart our seconds update timer
            self.start_timer()
        elif subone:
            # display the current remaining time at 0 seconds (after substracting the minute)
            # this is because the watch loop will substract this minute
            # right after the first watch payload returns with a time update
            self._update_time(0)
        else:
            # display full time with no substracting
            self._update_time(60)


class ConsoleOutput:
    def __init__(self, manager: GUIManager, master: tk.Misc):
        frame, body = make_card(master, "ACTIVITY", small=True)
        frame.grid(column=0, row=2, sticky="nsew")
        body.rowconfigure(0, weight=1)  # let the frame expand
        body.columnconfigure(0, weight=1)
        self._text = ctk.CTkTextbox(
            body,
            width=260,
            height=160,
            wrap="word",
            state="disabled",
            corner_radius=8,
            fg_color=PALETTE["bg"],
            text_color=PALETTE["fg"],
            font=ctk.CTkFont(family="Courier New", size=11),
        )
        self._text.grid(column=0, row=0, sticky="nsew")

    def print(self, message: str):
        stamp = datetime.now().strftime("%X")
        if '\n' in message:
            message = message.replace('\n', f"\n{stamp}: ")
        self._text.configure(state="normal")
        self._text.insert("end", f"{stamp}: {message}\n")
        self._text.see("end")  # scroll to the newly added line
        self._text.configure(state="disabled")


class _ChannelRow(TypedDict):
    frame: ctk.CTkFrame
    avatar: ctk.CTkLabel
    avatar_url: URLType | None
    name_label: ctk.CTkLabel
    badge: ctk.CTkFrame
    game_label: ctk.CTkLabel
    viewers_label: ctk.CTkLabel
    status_dot: ctk.CTkFrame
    status_label: ctk.CTkLabel


class ChannelList:
    """
    A custom scrollable list of per-channel row widgets (avatar dot, name +
    "WATCHING" badge, game, viewers, colored status dot+text) instead of a
    ttk.Treeview table - this is what it takes to get pill badges and colored
    rows matching the Clarity mockup exactly, which a plain Treeview cell
    (plain text only) can't render. Column widths are fixed pixel minsizes
    shared between the header row and every data row, so they line up.

    NOTE: the original Treeview had two extra trailing columns (a drops-
    enabled and an ACL-allowed indicator per channel) that the mockup doesn't
    have. Dropped to match it exactly; that data still drives the app's
    actual channel selection internally, it's just not shown here anymore.
    """
    # (minsize px, stretch weight) per column - shared by the header row and every
    # data row, so they both grow in lockstep and the table fills the card's width
    # instead of leaving a dead gap after the last column.
    _COLUMNS = ((34, 0), (170, 3), (150, 2), (90, 1), (110, 1), (40, 0))

    def __init__(self, manager: GUIManager, master: tk.Misc):
        self._manager = manager
        outer = ctk.CTkFrame(
            master,
            corner_radius=14,
            fg_color=PALETTE["surface"],
            border_width=1,
            border_color=PALETTE["border"],
        )
        self._frame = outer
        outer.grid(column=0, row=1, sticky="nsew")
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(2, weight=1)

        title_row = ctk.CTkFrame(outer, fg_color="transparent")
        title_row.grid(column=0, row=0, sticky="ew", padx=14, pady=(12, 10))
        title_row.columnconfigure(0, weight=1)
        ctk.CTkLabel(
            title_row,
            text=_("gui", "channels", "name"),
            font=ctk.CTkFont(weight="bold"),
            text_color=PALETTE["fg"],
            anchor="w",
        ).grid(column=0, row=0, sticky="w")
        self._switch_button = ctk.CTkButton(
            title_row,
            text=_("gui", "channels", "switch"),
            state="disabled",
            command=manager._twitch.state_change(State.CHANNEL_SWITCH),
            fg_color=PALETTE["surface"],
            hover_color=PALETTE["border"],
            text_color=PALETTE["accent"],
            border_width=1,
            border_color=PALETTE["accent"],
        )
        self._switch_button.grid(column=1, row=0, sticky="e")

        header_row = ctk.CTkFrame(outer, fg_color="transparent")
        header_row.grid(column=0, row=1, sticky="ew", padx=(20, 14))
        self._configure_columns(header_row)
        header_font = ctk.CTkFont(size=11, weight="bold")
        headings = (
            _("gui", "channels", "headings", "channel"),
            _("gui", "channels", "headings", "game"),
            _("gui", "channels", "headings", "viewers"),
            _("gui", "channels", "headings", "status"),
        )
        for i, text in enumerate(headings, start=1):
            ctk.CTkLabel(
                header_row, text=text.upper(), font=header_font, text_color=PALETTE["muted"],
                anchor="w",
            ).grid(column=i, row=0, sticky="w")

        self._rows_area = ctk.CTkScrollableFrame(outer, fg_color="transparent")
        self._rows_area.grid(column=0, row=2, sticky="nsew", padx=6, pady=(4, 10))
        self._rows_area.columnconfigure(0, weight=1)

        self._avatar_icon = circle_icon(18, "#9ca3af")
        self._rows: dict[str, _ChannelRow] = {}
        self._row_order: list[str] = []
        self._channel_map: dict[str, Channel] = {}
        self._watching_iid: str | None = None
        self._selected_iid: str | None = None
        self._watching_bg: str = PALETTE["sel"][0]
        self._status_colors: dict[str, str] = {
            "online": "#12b76a", "pending": "#dc6803", "offline": "#6b7280",
        }

    def _configure_columns(self, frame: ctk.CTkFrame) -> None:
        for i, (minsize, weight) in enumerate(self._COLUMNS):
            frame.columnconfigure(i, minsize=minsize, weight=weight)

    def configure_theme(
        self, *, watching_bg: str, online_fg: str, pending_fg: str, offline_fg: str
    ) -> None:
        self._watching_bg = watching_bg
        self._status_colors = {"online": online_fg, "pending": pending_fg, "offline": offline_fg}
        for iid in self._rows:
            self._restyle_row(iid)

    def _restyle_row(self, iid: str) -> None:
        row = self._rows[iid]
        if iid == self._selected_iid:
            bg = PALETTE["sel"]
        elif iid == self._watching_iid:
            bg = self._watching_bg
        else:
            bg = "transparent"
        row["frame"].configure(fg_color=bg)
        if iid == self._watching_iid:
            row["badge"].grid()
        else:
            row["badge"].grid_remove()

    def _select_row(self, iid: str, _event: tk.Event[Any] | None = None) -> None:
        if self._selected_iid == iid:
            return
        old = self._selected_iid
        self._selected_iid = iid
        if old is not None and old in self._rows:
            self._restyle_row(old)
        self._restyle_row(iid)
        self._switch_button.configure(state="normal")

    def get_selection(self) -> Channel | None:
        if self._selected_iid is None:
            return None
        return self._channel_map.get(self._selected_iid)

    def clear_selection(self) -> None:
        old = self._selected_iid
        self._selected_iid = None
        if old is not None and old in self._rows:
            self._restyle_row(old)
        self._switch_button.configure(state="disabled")

    def clear_watching(self) -> None:
        old = self._watching_iid
        self._watching_iid = None
        if old is not None and old in self._rows:
            self._restyle_row(old)

    def set_watching(self, channel: Channel) -> None:
        self.clear_watching()
        iid = channel.iid
        self._watching_iid = iid
        if iid in self._rows:
            self._restyle_row(iid)

    def clear(self) -> None:
        for row in self._rows.values():
            row["frame"].destroy()
        self._rows.clear()
        self._row_order.clear()
        self._channel_map.clear()
        self._watching_iid = None
        self._selected_iid = None

    def _build_row(self, iid: str) -> _ChannelRow:
        frame = ctk.CTkFrame(self._rows_area, corner_radius=8, fg_color="transparent")
        frame.grid(column=0, row=len(self._row_order), sticky="ew", pady=1)
        self._configure_columns(frame)

        avatar = ctk.CTkLabel(frame, text='', image=self._avatar_icon)
        avatar.grid(column=0, row=0, pady=7)

        name_box = ctk.CTkFrame(frame, fg_color="transparent")
        name_box.grid(column=1, row=0, sticky="w")
        name_label = ctk.CTkLabel(
            name_box, text='', font=ctk.CTkFont(weight="bold"), text_color=PALETTE["fg"],
            anchor="w",
        )
        name_label.grid(column=0, row=0, sticky="w")
        badge = ctk.CTkFrame(name_box, corner_radius=999, fg_color=PALETTE["sel"])
        ctk.CTkLabel(
            badge,
            text="WATCHING",
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color=PALETTE["accent"],
        ).grid(column=0, row=0, padx=8, pady=2)
        badge.grid(column=1, row=0, padx=(8, 0))
        badge.grid_remove()

        game_label = ctk.CTkLabel(frame, text='', text_color=PALETTE["muted"], anchor="w")
        game_label.grid(column=2, row=0, sticky="w")
        viewers_label = ctk.CTkLabel(frame, text='', text_color=PALETTE["muted"], anchor="w")
        viewers_label.grid(column=3, row=0, sticky="w")

        status_box = ctk.CTkFrame(frame, fg_color="transparent")
        status_box.grid(column=4, row=0, sticky="w")
        status_dot = ctk.CTkFrame(
            status_box, width=6, height=6, corner_radius=3, fg_color=PALETTE["muted"],
        )
        status_dot.grid(column=0, row=0, padx=(0, 6))
        status_label = ctk.CTkLabel(status_box, text='', anchor="w")
        status_label.grid(column=1, row=0, sticky="w")

        # dedicated column: a Twitch-glyph button that opens the channel in the browser
        open_button = ctk.CTkButton(
            frame,
            text="↗",  # external-link arrow
            width=28,
            height=28,
            corner_radius=8,
            fg_color="transparent",
            hover_color=PALETTE["border"],
            text_color=PALETTE["accent"],
            font=ctk.CTkFont(size=14, weight="bold"),
            command=partial(self._open_channel, iid),
        )
        open_button.grid(column=5, row=0)

        row = _ChannelRow(
            frame=frame,
            avatar=avatar,
            avatar_url=None,
            name_label=name_label,
            badge=badge,
            game_label=game_label,
            viewers_label=viewers_label,
            status_dot=status_dot,
            status_label=status_label,
        )
        for widget in (
            frame, avatar, name_box, name_label, game_label, viewers_label,
            status_box, status_dot, status_label,
        ):
            widget.bind("<Button-1>", partial(self._select_row, iid))
        return row

    def _open_channel(self, iid: str, _event: tk.Event[Any] | None = None) -> None:
        channel = self._channel_map.get(iid)
        if channel is not None:
            webopen(channel.url)

    def display(self, channel: Channel, *, add: bool = False) -> None:
        iid = channel.iid
        if iid not in self._channel_map and not add:
            # the channel isn't on the list and we're not supposed to add it
            return
        if channel.online:
            status = _("gui", "channels", "online")
            status_key = "online"
        elif channel.pending_online:
            status = _("gui", "channels", "pending")
            status_key = "pending"
        else:
            status = _("gui", "channels", "offline")
            status_key = "offline"
        game = str(channel.game or '')
        viewers = str(channel.viewers) if channel.viewers is not None else ''

        if iid in self._rows:
            row = self._rows[iid]
        else:
            self._channel_map[iid] = channel
            row = self._rows[iid] = self._build_row(iid)
            self._row_order.append(iid)

        row["name_label"].configure(text=channel.name)
        row["game_label"].configure(text=game)
        row["viewers_label"].configure(text=viewers)
        color = self._status_colors.get(status_key, PALETTE["muted"][0])
        row["status_label"].configure(text=status, text_color=color)
        row["status_dot"].configure(fg_color=color)
        self._restyle_row(iid)
        avatar_url = channel.profile_image_url
        if avatar_url is not None and avatar_url != row["avatar_url"]:
            row["avatar_url"] = avatar_url
            asyncio.create_task(self._load_avatar(row["avatar"], avatar_url))

    async def _load_avatar(self, avatar: ctk.CTkLabel, url: URLType) -> None:
        size = 18
        source = await self._manager._cache.get_image(url)
        source = source.convert("RGB").resize((size, size), Image_module.Resampling.LANCZOS)
        # mask to a circle, to match the generic placeholder dot's shape
        mask = Image_module.new("L", (size, size), 0)
        ImageDraw.Draw(mask).ellipse((0, 0, size - 1, size - 1), fill=255)
        circular = Image_module.new("RGBA", (size, size))
        circular.paste(source, mask=mask)
        photo = PhotoImage(master=self._manager._root, image=circular)
        with suppress(tk.TclError):
            avatar.configure(image=photo)

    def remove(self, channel: Channel) -> None:
        iid = channel.iid
        row = self._rows.pop(iid, None)
        if row is not None:
            row["frame"].destroy()
        if iid in self._row_order:
            self._row_order.remove(iid)
        del self._channel_map[iid]
        if self._watching_iid == iid:
            self._watching_iid = None
        if self._selected_iid == iid:
            self._selected_iid = None


class TrayIcon:
    TITLE = "Twitch Drops Miner"

    def __init__(self, manager: GUIManager, master: ttk.Widget):
        self._manager = manager
        self.icon: pystray.Icon | None = None  # type: ignore[unused-ignore]
        self._icon_images: dict[str, Image_module.Image] = {
            "pickaxe": Image_module.open(resource_path("icons/pickaxe.ico")),
            "active": Image_module.open(resource_path("icons/active.ico")),
            "idle": Image_module.open(resource_path("icons/idle.ico")),
            "error": Image_module.open(resource_path("icons/error.ico")),
            "maint": Image_module.open(resource_path("icons/maint.ico")),
        }
        self._icon_state: str = "pickaxe"
        self._button = ctk.CTkButton(
            master,
            command=self.minimize,
            text=_("gui", "tray", "minimize"),
            fg_color=PALETTE["surface"],
            hover_color=PALETTE["border"],
            text_color=PALETTE["fg"],
            border_width=1,
            border_color=PALETTE["border"],
            width=150,
            height=30,
        )

        # Hides Tray button for macOS
        if sys.platform != "darwin":
            self._button.grid(column=3, row=0, sticky="e", padx=(0, 14), pady=10)

    def __del__(self) -> None:
        self.stop()
        for icon_image in self._icon_images.values():
            icon_image.close()

    def _shorten(self, text: str, by_len: int, min_len: int) -> str:
        if (text_len := len(text)) <= min_len + 3 or by_len <= 0:
            # cannot shorten
            return text
        return text[:-min(by_len + 3, text_len - min_len)] + "..."

    def get_title(self, drop: TimedDrop | None) -> str:
        if drop is None:
            return self.TITLE
        campaign = drop.campaign
        title_parts: list[str] = [
            f"{self.TITLE}\n",
            f"{campaign.game.name}\n",
            drop.rewards_text(),
            f" {drop.progress:.1%} ({campaign.claimed_drops}/{campaign.total_drops})"
        ]
        min_len: int = 30
        max_len: int = 127
        missing_len = len(''.join(title_parts)) - max_len
        if missing_len > 0:
            # try shortening the reward text
            title_parts[2] = self._shorten(title_parts[2], missing_len, min_len)
            missing_len = len(''.join(title_parts)) - max_len
        if missing_len > 0:
            # try shortening the game name
            title_parts[1] = self._shorten(title_parts[1], missing_len, min_len)
            missing_len = len(''.join(title_parts)) - max_len
        if missing_len > 0:
            raise MinerException(f"Title couldn't be shortened: {''.join(title_parts)}")
        return ''.join(title_parts)

    def _start(self):
        loop = asyncio.get_running_loop()
        drop = self._manager.progress._drop

        # we need this because tray icon lives in a separate thread
        def bridge(func):
            return lambda: loop.call_soon_threadsafe(func)

        menu = pystray.Menu(
            pystray.MenuItem(_("gui", "tray", "show"), bridge(self.restore), default=True),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem(_("gui", "tray", "quit"), bridge(self.quit)),
        )
        self.icon = pystray.Icon(
            "twitch_miner", self._icon_images[self._icon_state], self.get_title(drop), menu
        )
        # self.icon.run_detached()
        loop.run_in_executor(None, self.icon.run)

    def stop(self):
        if self.icon is not None:
            self.icon.stop()
            self.icon = None

    def quit(self):
        self._manager.close()

    def minimize(self):
        if sys.platform == "darwin":
            return
        if self.icon is None:
            self._start()
        else:
            self.icon.visible = True
        self._manager._root.withdraw()

    def restore(self):
        if self.icon is not None:
            # self.stop()
            self.icon.visible = False
        self._manager._root.deiconify()

    def notify(
        self, message: str, title: str | None = None, duration: float = 10
    ) -> asyncio.Task[None] | None:
        # do nothing if the user disabled notifications
        if not self._manager._twitch.settings.tray_notifications:
            return None
        if self.icon is not None:
            icon = self.icon  # nonlocal scope bind

            async def notifier():
                icon.notify(message, title)
                await asyncio.sleep(duration)
                icon.remove_notification()

            return asyncio.create_task(notifier())
        return None

    def update_title(self, drop: TimedDrop | None):
        if self.icon is not None:
            self.icon.title = self.get_title(drop)

    def change_icon(self, state: str):
        if state not in self._icon_images:
            raise ValueError("Invalid icon state")
        self._icon_state = state
        if self.icon is not None:
            self.icon.icon = self._icon_images[state]


class Notebook:
    """
    Manual tab-switching content area: one CTkFrame per tab, only one gridded
    (visible) at a time. The actual tab *buttons* live in GUIManager's own top
    bar (a CTkSegmentedButton, alongside the brand/account chip) and drive this
    purely through select(name) - this class owns none of that chrome, only
    the stack of content frames beneath it.
    """
    def __init__(self, manager: GUIManager, master: tk.Misc):
        self._manager = manager
        # row 0 of master is the top bar (built by GUIManager); tab content goes below it
        master.rowconfigure(1, weight=1)
        master.columnconfigure(0, weight=1)
        self._master = master
        self._frames: dict[str, ctk.CTkFrame] = {}
        self._names: list[str] = []
        self._current: str | None = None
        self._view_callbacks: list[abc.Callable[[tk.Event[Any] | None], Any]] = []

    def add_tab(self, *, name: str) -> ctk.CTkFrame:
        frame = ctk.CTkFrame(self._master, fg_color="transparent")
        frame.grid(column=0, row=1, sticky="nsew")
        if self._current is None:
            self._current = name
        else:
            frame.grid_remove()
        self._frames[name] = frame
        self._names.append(name)
        return frame

    def select(self, name: str) -> None:
        if name == self._current or name not in self._frames:
            return
        assert self._current is not None
        self._frames[self._current].grid_remove()
        self._current = name
        self._frames[name].grid()
        # prevent entries from being selected after switching tabs
        self._manager._root.focus_set()
        for callback in self._view_callbacks:
            callback(None)

    def current_tab(self) -> int:
        if self._current in self._names:
            return self._names.index(self._current)
        return 0

    def add_view_event(self, callback: abc.Callable[[tk.Event[Any] | None], Any]):
        self._view_callbacks.append(callback)


class CampaignDisplay(TypedDict):
    frame: ctk.CTkFrame
    status: ctk.CTkLabel


class InventoryOverview:
    def __init__(self, manager: GUIManager, master: tk.Misc):
        self._manager = manager
        self._cache: ImageCache = manager._cache
        self._settings: Settings = manager._twitch.settings
        self._filters = {
            "not_linked": IntVar(
                master, self._settings.priority_mode is PriorityMode.PRIORITY_ONLY
            ),
            "upcoming": IntVar(master, 1),
            "expired": IntVar(master, 0),
            "excluded": IntVar(master, 0),
            "finished": IntVar(master, 0),
        }
        manager.tabs.add_view_event(self._on_tab_switched)

        def filter_check(key: str, text_key: str) -> ctk.CTkCheckBox:
            return ctk.CTkCheckBox(
                filter_frame,
                text=_("gui", "inventory", "filter", text_key),
                variable=self._filters[key],
                fg_color=PALETTE["accent"],
                hover_color=PALETTE["accent_hover"],
                checkmark_color=PALETTE["on_accent"],
                border_color=PALETTE["border"],
                text_color=PALETTE["fg"],
            )

        # Filtering options
        filter_outer, filter_frame = make_card(master, _("gui", "inventory", "filter", "name"))
        filter_outer.grid(column=0, row=0, columnspan=2, sticky="nsew")
        ctk.CTkLabel(
            filter_frame, text=_("gui", "inventory", "filter", "show"), text_color=PALETTE["fg"]
        ).grid(column=0, row=0, padx=(0, 10))
        icolumn = 0
        filter_check("not_linked", "not_linked").grid(
            column=(icolumn := icolumn + 1), row=0, padx=(0, 16)
        )
        filter_check("upcoming", "upcoming").grid(
            column=(icolumn := icolumn + 1), row=0, padx=(0, 16)
        )
        filter_check("expired", "expired").grid(
            column=(icolumn := icolumn + 1), row=0, padx=(0, 16)
        )
        filter_check("excluded", "excluded").grid(
            column=(icolumn := icolumn + 1), row=0, padx=(0, 16)
        )
        filter_check("finished", "finished").grid(
            column=(icolumn := icolumn + 1), row=0, padx=(0, 16)
        )
        ctk.CTkButton(
            filter_frame,
            text=_("gui", "inventory", "filter", "refresh"),
            command=self.refresh,
            fg_color=PALETTE["surface"],
            hover_color=PALETTE["border"],
            text_color=PALETTE["accent"],
            border_width=1,
            border_color=PALETTE["accent"],
        ).grid(column=(icolumn := icolumn + 1), row=0)
        # Inventory view - CTkScrollableFrame manages its own scrollbar and mousewheel binding
        self._main_frame = ctk.CTkScrollableFrame(
            master, fg_color="transparent", scrollbar_button_color=PALETTE["border"],
        )
        self._main_frame.grid(column=0, row=1, columnspan=2, sticky="nsew")
        self._main_frame.columnconfigure(0, weight=1)
        master.rowconfigure(1, weight=1)
        master.columnconfigure(0, weight=1)
        self._campaigns: dict[DropsCampaign, CampaignDisplay] = {}
        self._drops: dict[str, ctk.CTkLabel] = {}

    def _update_visibility(self, campaign: DropsCampaign):
        # True if the campaign is supposed to show, False makes it hidden.
        frame = self._campaigns[campaign]["frame"]
        not_linked = bool(self._filters["not_linked"].get())
        expired = bool(self._filters["expired"].get())
        excluded = bool(self._filters["excluded"].get())
        upcoming = bool(self._filters["upcoming"].get())
        finished = bool(self._filters["finished"].get())
        priority_only = self._settings.priority_mode is PriorityMode.PRIORITY_ONLY
        if (
            campaign.required_minutes > 0  # don't show sub-only campaigns
            and (not_linked or campaign.eligible)
            and (campaign.active or upcoming and campaign.upcoming or expired and campaign.expired)
            and (
                excluded or (
                    campaign.game.name not in self._settings.exclude
                    and not priority_only or campaign.game.name in self._settings.priority
                )
            )
            and (finished or not campaign.finished)
        ):
            frame.grid()
        else:
            frame.grid_remove()

    def _on_tab_switched(self, event: tk.Event[Any] | None) -> None:
        if self._manager.tabs.current_tab() == 1:
            # refresh only if we're switching to the tab
            self.refresh()

    def get_status(self, campaign: DropsCampaign) -> tuple[str, str]:
        if campaign.active:
            status_text: str = _("gui", "inventory", "status", "active")
            status_color: str = "#12b76a"
        elif campaign.upcoming:
            status_text = _("gui", "inventory", "status", "upcoming")
            status_color = "#dc6803"
        else:
            status_text = _("gui", "inventory", "status", "expired")
            status_color = "#f04438"
        return (status_text, status_color)

    def refresh(self):
        for campaign in self._campaigns:
            # status
            status_label = self._campaigns[campaign]["status"]
            status_text, status_color = self.get_status(campaign)
            status_label.configure(text=status_text, text_color=status_color)
            # visibility
            self._update_visibility(campaign)

    async def add_campaign(self, campaign: DropsCampaign) -> None:
        campaign_frame = ctk.CTkFrame(
            self._main_frame,
            corner_radius=12,
            fg_color=PALETTE["surface"],
            border_width=1,
            border_color=PALETTE["border"],
        )
        campaign_frame.grid(column=0, row=len(self._campaigns), sticky="nsew", pady=4, padx=2)
        campaign_frame.rowconfigure(4, weight=1)
        campaign_frame.columnconfigure(1, weight=1)
        campaign_frame.columnconfigure(3, weight=10000)
        # Name
        ctk.CTkLabel(
            campaign_frame,
            text=campaign.name,
            takefocus=False,
            width=320,
            anchor="w",
            font=ctk.CTkFont(weight="bold"),
            text_color=PALETTE["fg"],
        ).grid(column=0, row=0, columnspan=2, sticky="w", padx=6, pady=(6, 0))
        # Status
        status_text, status_color = self.get_status(campaign)
        status_label = ctk.CTkLabel(
            campaign_frame, text=status_text, takefocus=False, text_color=status_color,
        )
        status_label.grid(column=1, row=1, sticky="w", padx=4)
        # NOTE: We have to save the campaign's frame and status before any awaits happen,
        # otherwise the len(self._campaigns) call may overwrite an existing frame,
        # if the campaigns are added concurrently.
        self._campaigns[campaign] = {
            "frame": campaign_frame,
            "status": status_label,
        }
        # Starts / Ends
        MouseOverLabel(
            campaign_frame,
            text=_("gui", "inventory", "ends").format(
                time=campaign.ends_at.astimezone().replace(microsecond=0, tzinfo=None)
            ),
            alt_text=_("gui", "inventory", "starts").format(
                time=campaign.starts_at.astimezone().replace(microsecond=0, tzinfo=None)
            ),
            reverse=campaign.upcoming,
            takefocus=False,
            text_color=PALETTE["muted"],
        ).grid(column=1, row=2, sticky="w", padx=4)
        # Linking status
        if campaign.eligible:
            link_kwargs = {
                "plain": True,
                "text": _("gui", "inventory", "status", "linked"),
                "text_color": "#12b76a",
            }
        else:
            link_kwargs = {
                "text": _("gui", "inventory", "status", "not_linked"),
                "text_color": "#f04438",
            }
        LinkLabel(
            campaign_frame,
            link=campaign.link_url,
            takefocus=False,
            **link_kwargs,
        ).grid(column=1, row=3, sticky="w", padx=4)
        # ACL channels
        acl = campaign.allowed_channels
        if acl:
            if len(acl) <= 5:
                allowed_text: str = '\n'.join(ch.name for ch in acl)
            else:
                allowed_text = '\n'.join(ch.name for ch in acl[:4])
                allowed_text += (
                    f"\n{_('gui', 'inventory', 'and_more').format(amount=len(acl) - 4)}"
                )
        else:
            allowed_text = _("gui", "inventory", "all_channels")
        ctk.CTkLabel(
            campaign_frame,
            text=f"{_('gui', 'inventory', 'allowed_channels')}\n{allowed_text}",
            takefocus=False,
            justify="left",
            anchor="w",
            text_color=PALETTE["muted"],
        ).grid(column=1, row=4, sticky="nw", padx=4, pady=(0, 6))
        # Image (stays a plain ttk.Label - CTkLabel's image param expects a CTkImage,
        # not the plain PIL PhotoImage the cache hands out)
        campaign_image = await self._cache.get(campaign.image_url, size=(108, 144))
        ttk.Label(campaign_frame, image=campaign_image).grid(
            column=0, row=1, rowspan=4, padx=6, pady=6
        )
        # Drops separator
        ctk.CTkFrame(
            campaign_frame, width=1, fg_color=PALETTE["border"]
        ).grid(column=2, row=0, rowspan=5, sticky="ns", pady=6)
        # Drops display
        drops_row = ctk.CTkFrame(campaign_frame, fg_color="transparent")
        drops_row.grid(column=3, row=0, rowspan=5, sticky="nsew", padx=4, pady=6)
        drops_row.rowconfigure(0, weight=1)
        for i, drop in enumerate(campaign.drops):
            drop_frame = ctk.CTkFrame(
                drops_row,
                corner_radius=10,
                fg_color=PALETTE["bg"],
                border_width=1,
                border_color=PALETTE["border"],
            )
            drop_frame.grid(column=i, row=0, padx=4)
            benefits_frame = ctk.CTkFrame(drop_frame, fg_color="transparent")
            benefits_frame.grid(column=0, row=0, padx=5, pady=5)
            benefit_images: list[PhotoImage] = await asyncio.gather(
                *(self._cache.get(benefit.image_url, (80, 80)) for benefit in drop.benefits)
            )
            for i, benefit, image in zip(range(len(drop.benefits)), drop.benefits, benefit_images):
                # plain ttk.Label here too, for the same CTkImage-vs-PhotoImage reason as above
                ttk.Label(
                    benefits_frame,
                    text=benefit.name,
                    image=image,
                    compound="bottom",
                ).grid(column=i, row=0, padx=5)
            self._drops[drop.id] = label = ctk.CTkLabel(
                drop_frame, justify="center", text_color=PALETTE["fg"]
            )
            self.update_progress(drop, label)
            label.grid(column=0, row=1, pady=(0, 5))
        if self._manager.tabs.current_tab() == 1:
            self._update_visibility(campaign)

    def clear(self) -> None:
        for child in self._main_frame.winfo_children():
            child.destroy()
        self._drops.clear()
        self._campaigns.clear()

    def update_progress(self, drop: TimedDrop, label: ctk.CTkLabel) -> None:
        progress_text: str
        progress_color: str = ''
        if drop.is_claimed:
            progress_color = "#12b76a"
            progress_text = _("gui", "inventory", "status", "claimed")
        elif drop.can_claim:
            progress_color = "#dc6803"
            progress_text = _("gui", "inventory", "status", "ready_to_claim")
        elif drop.current_minutes or drop.can_earn():
            progress_text = _("gui", "inventory", "percent_progress").format(
                percent=f"{drop.progress:3.1%}",
                minutes=drop.required_minutes,
            )
            if drop.ends_at < drop.campaign.ends_at:
                # this drop becomes unavailable earlier than the campaign ends
                progress_text += '\n' + _("gui", "inventory", "ends").format(
                    time=drop.ends_at.astimezone().replace(microsecond=0, tzinfo=None)
                )
        else:
            if drop.required_minutes > 0:
                progress_text = _("gui", "inventory", "minutes_progress").format(
                    minutes=drop.required_minutes
                )
            else:
                # required_minutes is zero for subscription-based drops
                progress_text = ''
            if datetime.now(timezone.utc) < drop.starts_at > drop.campaign.starts_at:
                # this drop can only be earned later than the campaign start
                progress_text += '\n' + _("gui", "inventory", "starts").format(
                    time=drop.starts_at.astimezone().replace(microsecond=0, tzinfo=None)
                )
            elif drop.ends_at < drop.campaign.ends_at:
                # this drop becomes unavailable earlier than the campaign ends
                progress_text += '\n' + _("gui", "inventory", "ends").format(
                    time=drop.ends_at.astimezone().replace(microsecond=0, tzinfo=None)
                )
        label.configure(text=progress_text, text_color=progress_color or PALETTE["fg"])

    def update_drop(self, drop: TimedDrop) -> None:
        label = self._drops.get(drop.id)
        if label is None:
            return
        self.update_progress(drop, label)


def proxy_validate(entry: PlaceholderEntry, settings: Settings) -> bool:
    raw_url = entry.get().strip()
    entry.replace(raw_url)
    url = URL(raw_url)
    valid = url.host is not None and url.port is not None
    if not valid:
        entry.clear()
        url = URL()
    settings.proxy = url
    return valid


class _SettingsVars(TypedDict):
    tray: IntVar
    proxy: StringVar
    autostart: IntVar
    dark_mode: IntVar
    language: StringVar
    priority_mode: StringVar
    tray_notifications: IntVar
    enable_badges_emotes: IntVar
    available_drops_check: IntVar


class SettingsPanel:
    AUTOSTART_NAME: str = "TwitchDropsMiner"
    AUTOSTART_KEY: str = "HKCU/Software/Microsoft/Windows/CurrentVersion/Run"

    @cached_property
    def PRIORITY_MODES(self) -> dict[PriorityMode, str]:
        # NOTE: Translation calls have to be deferred here,
        # to allow changing the language before the settings panel is initialized.
        return {
            PriorityMode.PRIORITY_ONLY: _("gui", "settings", "priority_modes", "priority_only"),
            PriorityMode.ENDING_SOONEST: _("gui", "settings", "priority_modes", "ending_soonest"),
            PriorityMode.LOW_AVBL_FIRST: _(
                "gui", "settings", "priority_modes", "low_availability"
            ),
        }

    def __init__(self, manager: GUIManager, master: tk.Misc):
        self._manager = manager
        self._settings: Settings = manager._twitch.settings
        priority_mode = self._settings.priority_mode
        if priority_mode not in self.PRIORITY_MODES:
            priority_mode = PriorityMode.PRIORITY_ONLY
            self._settings.priority_mode = priority_mode
        self._vars: _SettingsVars = {
            "autostart": IntVar(master, 0),
            "language": StringVar(master, _.current),
            "proxy": StringVar(master, str(self._settings.proxy)),
            "tray": IntVar(master, self._settings.autostart_tray),
            "dark_mode": IntVar(master, int(self._settings.dark_mode)),
            "priority_mode": StringVar(master, self.PRIORITY_MODES[priority_mode]),
            "tray_notifications": IntVar(master, self._settings.tray_notifications),
            "enable_badges_emotes": IntVar(
                master, int(self._settings.enable_badges_emotes)
            ),
            "available_drops_check": IntVar(
                master, int(self._settings.available_drops_check)
            ),
        }
        self._game_names: set[str] = set()

        # Full-bleed 3-column layout: General+Advanced stacked on the left,
        # Priority and Exclude filling the full height on the right, and a
        # slim sticky Reload bar across the bottom - replacing the old
        # everything-crammed-into-one-centered-island layout.
        master.rowconfigure(0, weight=1)
        master.rowconfigure(1, weight=0)
        master.columnconfigure(0, weight=3)
        master.columnconfigure(1, weight=2)
        master.columnconfigure(2, weight=2)

        def label(parent: tk.Misc, key_path: tuple[str, ...], **kwargs) -> ctk.CTkLabel:
            kwargs.setdefault("text_color", PALETTE["fg"])
            kwargs.setdefault("anchor", "w")
            return ctk.CTkLabel(parent, text=_("gui", *key_path), **kwargs)

        def checkbox(parent: tk.Misc, variable: IntVar, command) -> ctk.CTkCheckBox:
            return ctk.CTkCheckBox(
                parent,
                text='',
                width=24,
                variable=variable,
                command=command,
                fg_color=PALETTE["accent"],
                hover_color=PALETTE["accent_hover"],
                checkmark_color=PALETTE["on_accent"],
                border_color=PALETTE["border"],
            )

        def icon_button(parent: tk.Misc, text: str, command, *, size: int = 14) -> ctk.CTkButton:
            return ctk.CTkButton(
                parent,
                text=text,
                command=command,
                width=36,
                font=ctk.CTkFont(size=size),
                fg_color=PALETTE["surface"],
                hover_color=PALETTE["border"],
                text_color=PALETTE["fg"],
                border_width=1,
                border_color=PALETTE["border"],
            )

        def setting_row(parent: tk.Misc, r: int, key_path: tuple[str, ...], control) -> None:
            label(parent, key_path).grid(column=0, row=r, sticky="w", pady=7)
            control.grid(column=1, row=r, sticky="e", pady=7)

        left_col = ctk.CTkFrame(master, fg_color="transparent")
        left_col.grid(column=0, row=0, sticky="nsew", padx=(0, 10))
        left_col.columnconfigure(0, weight=1)

        # General section
        general_outer, general_frame = make_card(
            left_col, _("gui", "settings", "general", "name")
        )
        general_outer.grid(column=0, row=0, sticky="new", pady=(0, 10))
        general_frame.columnconfigure(0, weight=1)

        setting_row(
            general_frame, 0, ("settings", "general", "autostart"),
            checkbox(general_frame, self._vars["autostart"], self.update_autostart),
        )
        self._vars["autostart"].set(self._query_autostart())
        grow = 1
        if sys.platform != "darwin":
            setting_row(
                general_frame, grow, ("settings", "general", "tray"),
                checkbox(general_frame, self._vars["tray"], self.update_autostart),
            )
            grow += 1
            setting_row(
                general_frame, grow, ("settings", "general", "tray_notifications"),
                checkbox(
                    general_frame,
                    self._vars["tray_notifications"],
                    lambda: setattr(
                        self._settings,
                        "tray_notifications",
                        bool(self._vars["tray_notifications"].get()),
                    ),
                ),
            )
            grow += 1
        setting_row(
            general_frame, grow, ("settings", "general", "dark_mode"),
            checkbox(general_frame, self._vars["dark_mode"], self.update_dark_mode),
        )
        grow += 1
        setting_row(
            general_frame, grow, ("settings", "general", "priority_mode"),
            SelectCombobox(
                general_frame,
                command=self.priority_mode,
                textvariable=self._vars["priority_mode"],
                values=list(self.PRIORITY_MODES.values()),
            ),
        )
        grow += 1
        ctk.CTkLabel(
            general_frame, text="Language 🌐 (requires restart)", text_color=PALETTE["fg"],
            anchor="w",
        ).grid(column=0, row=grow, sticky="w", pady=7)
        SelectCombobox(
            general_frame,
            values=list(_.languages),
            textvariable=self._vars["language"],
            command=lambda e: setattr(self._settings, "language", self._vars["language"].get()),
        ).grid(column=1, row=grow, sticky="e", pady=7)
        grow += 1

        make_separator(general_frame).grid(
            column=0, row=grow, columnspan=2, sticky="ew", pady=10
        )
        grow += 1
        label(general_frame, ("settings", "general", "proxy")).grid(
            column=0, row=grow, columnspan=2, sticky="w"
        )
        grow += 1
        self._proxy = PlaceholderEntry(
            general_frame,
            validate="focusout",
            prefill="http://",
            textvariable=self._vars["proxy"],
            placeholder="http://username:password@address:port",
        )
        self._proxy.configure(validatecommand=partial(proxy_validate, self._proxy, self._settings))
        self._proxy.grid(column=0, row=grow, columnspan=2, sticky="ew", pady=(4, 0))

        # Advanced section
        advanced_outer, advanced_frame = make_card(
            left_col, _("gui", "settings", "advanced", "name")
        )
        advanced_outer.grid(column=0, row=1, sticky="new")
        advanced_frame.columnconfigure(0, weight=1)

        ctk.CTkLabel(
            advanced_frame,
            text=_("gui", "settings", "advanced", "warning"),
            text_color=PALETTE["danger"],
            font=ctk.CTkFont(weight="bold"),
            anchor="w",
        ).grid(column=0, row=0, columnspan=2, sticky="w")
        ctk.CTkLabel(
            advanced_frame,
            text=_("gui", "settings", "advanced", "warning_text"),
            text_color=PALETTE["warn"],
            anchor="w",
            justify="left",
        ).grid(column=0, row=1, columnspan=2, sticky="w", pady=(2, 10))
        setting_row(
            advanced_frame, 2, ("settings", "advanced", "enable_badges_emotes"),
            checkbox(
                advanced_frame,
                self._vars["enable_badges_emotes"],
                lambda: setattr(
                    self._settings,
                    "enable_badges_emotes",
                    bool(self._vars["enable_badges_emotes"].get()),
                ),
            ),
        )
        setting_row(
            advanced_frame, 3, ("settings", "advanced", "available_drops_check"),
            checkbox(
                advanced_frame,
                self._vars["available_drops_check"],
                lambda: setattr(
                    self._settings,
                    "available_drops_check",
                    bool(self._vars["available_drops_check"].get()),
                ),
            ),
        )

        # Priority section - fills the full column height
        priority_outer, priority_frame = make_card(master, _("gui", "settings", "priority"))
        priority_outer.grid(column=1, row=0, sticky="nsew", padx=(0, 10))
        priority_frame.columnconfigure(0, weight=1)
        priority_frame.rowconfigure(1, weight=1)
        self._priority_entry = PlaceholderComboBox(
            priority_frame, placeholder=_("gui", "settings", "game_name")
        )
        self._priority_entry.grid(column=0, row=0, sticky="ew")
        icon_button(
            priority_frame, "➕", self.priority_add
        ).grid(column=1, row=0, sticky="nsew")
        self._priority_list = PaddedListbox(
            priority_frame,
            padding=(1, 0),
            activestyle="none",
            selectmode="single",
            highlightthickness=0,
            exportselection=False,
        )
        self._priority_list.grid(column=0, row=1, rowspan=5, sticky="nsew")
        self._priority_list.insert("end", *self._settings.priority)
        weight_scale: int = 5
        icon_button(  # Move to top
            priority_frame, "⇈", partial(self.priority_move, MAX_INT), size=16,
        ).grid(column=1, row=1, sticky="nsew")
        priority_frame.rowconfigure(1, weight=1)
        icon_button(  # Move up
            priority_frame, "↑", partial(self.priority_move, 1), size=16,
        ).grid(column=1, row=2, sticky="nsew")
        priority_frame.rowconfigure(2, weight=weight_scale)
        icon_button(  # Move down
            priority_frame, "↓", partial(self.priority_move, -1), size=16,
        ).grid(column=1, row=3, sticky="nsew")
        priority_frame.rowconfigure(3, weight=weight_scale)
        icon_button(  # Move to bottom
            priority_frame, "⇊", partial(self.priority_move, -MAX_INT), size=16,
        ).grid(column=1, row=4, sticky="nsew")
        priority_frame.rowconfigure(4, weight=1)
        icon_button(
            priority_frame, "❌", self.priority_delete
        ).grid(column=1, row=5, sticky="nsew")
        priority_frame.rowconfigure(5, weight=1)

        # Exclude section - fills the full column height
        exclude_outer, exclude_frame = make_card(master, _("gui", "settings", "exclude"))
        exclude_outer.grid(column=2, row=0, sticky="nsew")
        exclude_frame.columnconfigure(0, weight=1)
        exclude_frame.rowconfigure(1, weight=1)
        self._exclude_entry = PlaceholderComboBox(
            exclude_frame, placeholder=_("gui", "settings", "game_name")
        )
        self._exclude_entry.grid(column=0, row=0, sticky="ew")
        icon_button(
            exclude_frame, "➕", self.exclude_add
        ).grid(column=1, row=0)
        self._exclude_list = PaddedListbox(
            exclude_frame,
            padding=(1, 0),
            activestyle="none",
            selectmode="single",
            highlightthickness=0,
            exportselection=False,
        )
        self._exclude_list.grid(column=0, row=1, columnspan=2, sticky="nsew")
        # insert them alphabetically
        self._exclude_list.insert("end", *sorted(self._settings.exclude))
        icon_button(
            exclude_frame, "❌", self.exclude_delete
        ).grid(column=0, row=2, columnspan=2, sticky="nsew")

        # Reload bar - a slim sticky footer spanning all 3 columns
        reload_outer, reload_body = make_card(master, None)
        reload_outer.grid(column=0, row=1, columnspan=3, sticky="ew", pady=(10, 0))
        reload_body.columnconfigure(0, weight=1)
        ctk.CTkLabel(
            reload_body,
            text=_("gui", "settings", "reload_text"),
            text_color=PALETTE["muted"],
            anchor="w",
        ).grid(column=0, row=0, sticky="w")
        ctk.CTkButton(
            reload_body,
            text=_("gui", "settings", "reload"),
            command=self._manager._twitch.state_change(State.INVENTORY_FETCH),
            font=ctk.CTkFont(weight="bold"),
            fg_color=PALETTE["accent"],
            hover_color=PALETTE["accent_hover"],
            text_color=PALETTE["on_accent"],
        ).grid(column=1, row=0, sticky="e")

    def clear_selection(self) -> None:
        self._priority_list.selection_clear(0, "end")
        self._exclude_list.selection_clear(0, "end")

    def update_dark_mode(self) -> None:
        self._settings.dark_mode = bool(self._vars["dark_mode"].get())
        self._manager.apply_theme(self._settings.dark_mode)

    def _get_self_path(self) -> str:
        # NOTE: we need double quotes in case the path contains spaces
        return f'"{SELF_PATH.resolve()!s}"'

    def _get_autostart_path(self) -> str:
        flags: list[str] = []
        # if applicable, include the current logging level as well
        for lvl_idx, lvl_value in LOGGING_LEVELS.items():
            if lvl_value == self._settings.logging_level:
                if lvl_idx > 0:
                    flags.append(f"-{'v' * lvl_idx}")
                break
        if self._vars["tray"].get():
            flags.append("--tray")
        if not IS_PACKAGED:
            # non-packaged autostart has to be done through the venv path pythonw
            return f"\"{SCRIPTS_PATH / 'pythonw'!s}\" {self._get_self_path()} {' '.join(flags)}"
        return f"{self._get_self_path()} {' '.join(flags)}"

    def _get_linux_autostart_filepath(self) -> Path:
        autostart_folder: Path = Path("~/.config/autostart").expanduser()
        if (config_home := os.environ.get("XDG_CONFIG_HOME")) is not None:
            config_autostart: Path = Path(config_home, "autostart").expanduser()
            if config_autostart.exists():
                autostart_folder = config_autostart
        return autostart_folder / f"{self.AUTOSTART_NAME}.desktop"

    def _get_mac_autostart_filepath(self) -> Path:
        return Path(
            Path.home(), f"Library/LaunchAgents/com.devilxd.{self.AUTOSTART_NAME.lower()}.plist"
        )

    def _query_autostart(self) -> bool:
        if sys.platform == "win32":
            with RegistryKey(self.AUTOSTART_KEY, read_only=True) as key:
                try:
                    value_type, value = key.get(self.AUTOSTART_NAME)
                except ValueNotFound:
                    return False
                # TODO: Consider deleting the old value to avoid autostart errors
                return (
                    value_type is ValueType.REG_SZ
                    and self._get_self_path() in value
                )
        elif sys.platform == "linux":
            autostart_file: Path = self._get_linux_autostart_filepath()
            if not autostart_file.exists():
                return False
            with autostart_file.open('r', encoding="utf8") as file:
                # TODO: Consider deleting the old file to avoid autostart errors
                return self._get_self_path() in file.read()
        elif sys.platform == "darwin":
            plist_file = self._get_mac_autostart_filepath()
            if not plist_file.exists():
                return False
            with plist_file.open('r', encoding="utf8") as file:
                return str(SELF_PATH.resolve()) in file.read()

    def update_autostart(self) -> None:
        enabled = bool(self._vars["autostart"].get())
        self._settings.autostart_tray = bool(self._vars["tray"].get())
        if sys.platform == "win32":
            if enabled:
                with RegistryKey(self.AUTOSTART_KEY) as key:
                    key.set(
                        self.AUTOSTART_NAME,
                        ValueType.REG_SZ,
                        self._get_autostart_path(),
                    )
            else:
                with RegistryKey(self.AUTOSTART_KEY) as key:
                    key.delete(self.AUTOSTART_NAME, silent=True)
        elif sys.platform == "linux":
            autostart_file: Path = self._get_linux_autostart_filepath()
            if enabled:
                file_contents: str = dedent(
                    f"""
                    [Desktop Entry]
                    Type=Application
                    Name=Twitch Drops Miner
                    Description=Mine timed drops on Twitch
                    Exec=sh -c '{self._get_autostart_path()}'
                    """
                )
                with autostart_file.open('w', encoding="utf8") as file:
                    file.write(file_contents)
            else:
                autostart_file.unlink(missing_ok=True)
        elif sys.platform == "darwin":
            plist_file = self._get_mac_autostart_filepath()

            if enabled:
                command_parts = shlex.split(self._get_autostart_path())
                plist_data = {
                    "Label": f"com.devilxd.{self.AUTOSTART_NAME.lower()}",
                    "ProgramArguments": command_parts,
                    "RunAtLoad": True,
                }
                plist_file.parent.mkdir(parents=True, exist_ok=True)
                with plist_file.open("wb") as file:
                    plistlib.dump(plist_data, file)
            else:
                plist_file.unlink(missing_ok=True)

    def update_excluded_choices(self) -> None:
        self._exclude_entry.configure(
            values=sorted(self._game_names.difference(self._settings.exclude))
        )

    def update_priority_choices(self) -> None:
        self._priority_entry.configure(
            values=sorted(self._game_names.difference(self._settings.priority))
        )

    def set_games(self, games: set[Game]) -> None:
        self._game_names.update(game.name for game in games)
        self.update_excluded_choices()
        self.update_priority_choices()

    def priority_add(self) -> None:
        game_name: str = self._priority_entry.get()
        if not game_name:
            # prevent adding empty strings
            return
        self._priority_entry.clear()
        # add it preventing duplicates
        try:
            existing_idx: int = self._settings.priority.index(game_name)
        except ValueError:
            # not there, add it
            self._priority_list.insert("end", game_name)
            self._priority_list.see("end")
            self._settings.priority.append(game_name)
            self._settings.alter()
            self.update_priority_choices()
        else:
            # already there, set the selection on it
            self._priority_list.selection_set(existing_idx)
            self._priority_list.see(existing_idx)

    def _priority_idx(self) -> int | None:
        selection: tuple[int, ...] = self._priority_list.curselection()
        if not selection:
            return None
        return selection[0]

    def priority_move(self, amount: int) -> None:
        # amount > 0 = up, amount < 0 = down
        idx: int | None = self._priority_idx()
        max_idx: int = self._priority_list.size() - 1
        if (
            idx is None
            or amount == 0
            or amount > 0 and idx == 0
            or amount < 0 and idx == max_idx
        ):
            return
        insert_idx: int = idx - amount
        if insert_idx <= 0:
            insert_idx = 0
        elif insert_idx >= max_idx:
            insert_idx = max_idx

        item: str = self._priority_list.get(idx)
        self._priority_list.delete(idx)
        self._priority_list.insert(insert_idx, item)
        # reselect the item and scroll the list if needed
        self._priority_list.selection_set(insert_idx)
        self._priority_list.see(insert_idx)
        # update the underlying settings list too
        self._settings.priority.pop(idx)
        self._settings.priority.insert(insert_idx, item)
        self._settings.alter()

    def priority_delete(self) -> None:
        idx: int | None = self._priority_idx()
        if idx is None:
            return
        self._priority_list.delete(idx)
        del self._settings.priority[idx]
        self._settings.alter()
        self.update_priority_choices()

    def priority_mode(self, event: tk.Event[ttk.Combobox]) -> None:
        mode_name: str = self._vars["priority_mode"].get()
        for value, name in self.PRIORITY_MODES.items():
            if mode_name == name:
                self._settings.priority_mode = value
                break

    def exclude_add(self) -> None:
        game_name: str = self._exclude_entry.get()
        if not game_name:
            # prevent adding empty strings
            return
        self._exclude_entry.clear()
        if game_name not in self._settings.exclude:
            self._settings.exclude.add(game_name)
            self._settings.alter()
            self.update_excluded_choices()
            # insert it alphabetically
            for i, item in enumerate(self._exclude_list.get(0, "end")):
                if game_name < item:
                    self._exclude_list.insert(i, game_name)
                    self._exclude_list.see(i)
                    break
            else:
                self._exclude_list.insert("end", game_name)
                self._exclude_list.see("end")
        else:
            # it was already there, select it
            for i, item in enumerate(self._exclude_list.get(0, "end")):
                if item == game_name:
                    existing_idx = i
                    break
            else:
                # something went horribly wrong and it's not there after all - just return
                return
            self._exclude_list.selection_set(existing_idx)
            self._exclude_list.see(existing_idx)

    def exclude_delete(self) -> None:
        selection: tuple[int, ...] = self._exclude_list.curselection()
        if not selection:
            return None
        idx: int = selection[0]
        item: str = self._exclude_list.get(idx)
        if item in self._settings.exclude:
            self._exclude_list.delete(idx)
            self._settings.exclude.discard(item)
            self._settings.alter()
            self.update_excluded_choices()


class HelpTab:
    WIDTH = 800

    def __init__(self, manager: GUIManager, master: tk.Misc):
        self._twitch = manager._twitch
        master.rowconfigure(0, weight=1)
        master.columnconfigure(0, weight=1)
        # use a frame to center the content within the tab
        center_frame = ctk.CTkFrame(master, fg_color="transparent")
        center_frame.grid(column=0, row=0)
        # use a frame for the bottom row specifically
        bottom_frame = ctk.CTkFrame(master, fg_color="transparent")
        bottom_frame.grid(column=0, row=1, sticky="nsew")
        irow = 0
        # About
        about_outer, about = make_card(center_frame, "About")
        about_outer.grid(column=0, row=(irow := irow + 1), sticky="nsew", padx=2, pady=4)
        about.columnconfigure(2, weight=1)
        # About - created by
        ctk.CTkLabel(
            about, text="Application created by: ", anchor="e", text_color=PALETTE["fg"]
        ).grid(column=0, row=0, sticky="nsew")
        LinkLabel(
            about, link="https://github.com/DevilXD", text="DevilXD"
        ).grid(column=1, row=0, sticky="nsew")
        # About - repo link
        ctk.CTkLabel(
            about, text="Repository: ", anchor="e", text_color=PALETTE["fg"]
        ).grid(column=0, row=1, sticky="nsew")
        LinkLabel(
            about,
            link="https://github.com/DevilXD/TwitchDropsMiner",
            text="https://github.com/DevilXD/TwitchDropsMiner",
        ).grid(column=1, row=1, sticky="nsew")
        # About - donate
        make_separator(about).grid(column=0, row=2, columnspan=3, sticky="ew", pady=4)
        ctk.CTkLabel(
            about, text="Donate: ", anchor="e", text_color=PALETTE["fg"]
        ).grid(column=0, row=3, sticky="nsew")
        LinkLabel(
            about,
            link="https://www.buymeacoffee.com/DevilXD",
            text=(
                "If you like the application and found it useful, "
                "please consider donating a small amount of money to support me. Thank you!"
            ),
            wraplength=self.WIDTH,
            justify="left",
        ).grid(column=1, row=3, sticky="nsew")
        # Useful links
        links_outer, links = make_card(center_frame, _("gui", "help", "links", "name"))
        links_outer.grid(column=0, row=(irow := irow + 1), sticky="nsew", padx=2, pady=4)
        LinkLabel(
            links,
            link="https://www.twitch.tv/drops/inventory",
            text=_("gui", "help", "links", "inventory"),
        ).grid(column=0, row=0, sticky="nsew")
        LinkLabel(
            links,
            link="https://www.twitch.tv/drops/campaigns",
            text=_("gui", "help", "links", "campaigns"),
        ).grid(column=0, row=1, sticky="nsew")
        # How It Works
        howitworks_outer, howitworks = make_card(center_frame, _("gui", "help", "how_it_works"))
        howitworks_outer.grid(column=0, row=(irow := irow + 1), sticky="nsew", padx=2, pady=4)
        ctk.CTkLabel(
            howitworks,
            text=_("gui", "help", "how_it_works_text"),
            wraplength=self.WIDTH,
            justify="left",
            text_color=PALETTE["fg"],
        ).grid(sticky="nsew")
        getstarted_outer, getstarted = make_card(center_frame, _("gui", "help", "getting_started"))
        getstarted_outer.grid(column=0, row=(irow := irow + 1), sticky="nsew", padx=2, pady=4)
        ctk.CTkLabel(
            getstarted,
            text=_("gui", "help", "getting_started_text"),
            wraplength=self.WIDTH,
            justify="left",
            text_color=PALETTE["fg"],
        ).grid(sticky="nsew")

        # Invalidate button
        invalidate_frame = ctk.CTkFrame(bottom_frame, fg_color="transparent")
        bottom_frame.columnconfigure(0, weight=1)  # center within the column
        invalidate_frame.grid(column=0, row=0, sticky="nse")
        ctk.CTkLabel(
            invalidate_frame,
            text=_("gui", "help", "invalidate", "text"),
            text_color=PALETTE["fg"],
        ).grid(column=0, row=0)
        self._invalidate_button = ctk.CTkButton(
            invalidate_frame,
            text=_("gui", "help", "invalidate", "button"),
            command=self.invalidate_token,
            state="disabled",
            fg_color=PALETTE["danger"],
            hover_color=PALETTE["warn"],
            text_color=PALETTE["on_accent"],
        )
        self._invalidate_button.grid(column=1, row=0, padx=(8, 0))

    def invalidate_token(self) -> None:
        # sync to async bridge
        asyncio.create_task(task_wrapper(self._invalidate_token)())

    async def _invalidate_token(self) -> None:
        auth_state = await self._twitch.get_auth()
        async with self._twitch.request(
            "POST",
            "https://id.twitch.tv/oauth2/revoke",
            data={
                "client_id": self._twitch._client_type.CLIENT_ID,
                "token": auth_state.access_token,
            }
        ) as response:
            if response.status == 200:
                auth_state.invalidate(delete_cookies=True)
            else:
                logger.error(f"Failed to invalidate the auth token: {response.status}")
        self._twitch.change_state(State.RESTART)


##########################################
# GUI DEFINITION END / GUI MANAGER START #
##########################################


class GUIManager:
    def __init__(self, twitch: Twitch):
        self._twitch: Twitch = twitch
        self._poll_task: asyncio.Task[NoReturn] | None = None
        self._close_requested = asyncio.Event()
        # set the appearance mode before building any CTk widget, so nothing is ever
        # constructed in the wrong (System-detected) mode even for a single frame
        ctk.set_appearance_mode("dark" if twitch.settings.dark_mode else "light")
        self._root = root = ctk.CTk(className=WINDOW_TITLE)
        # withdraw immediately to prevent the window from flashing
        self._root.withdraw()
        # root.resizable(False, True)
        set_root_icon(root, resource_path("icons/pickaxe.ico"))
        root.title(WINDOW_TITLE)  # window title
        root.bind_all("<KeyPress-Escape>", self.unfocus)  # pressing ESC unfocuses selection
        # Image cache for displaying images
        self._cache = ImageCache(self)

        # style adjustements - only a couple of plain ttk.Label/Frame widgets remain
        # (image-bearing labels - see InventoryOverview.add_campaign), everything else
        # is CustomTkinter and is themed via the PALETTE (light, dark) tuples
        self._style = style = ttk.Style(root)
        if sys.platform != "darwin":
            style.theme_use("clam")
        # end of style changes

        root_frame = ctk.CTkFrame(root, fg_color="transparent")
        root_frame.grid(column=0, row=0, sticky="nsew", padx=8, pady=8)
        root.rowconfigure(0, weight=1)
        root.columnconfigure(0, weight=1)
        root_frame.rowconfigure(1, weight=1)
        root_frame.columnconfigure(0, weight=1)

        # Top bar: brand, nav pills, account status, tray button - all in one row
        topbar = ctk.CTkFrame(
            root_frame,
            corner_radius=14,
            fg_color=PALETTE["surface"],
            border_width=1,
            border_color=PALETTE["border"],
        )
        topbar.grid(column=0, row=0, sticky="ew", pady=(0, 10))
        topbar.columnconfigure(1, weight=1)
        brand = ctk.CTkFrame(topbar, fg_color="transparent")
        brand.grid(column=0, row=0, sticky="w", padx=14, pady=10)
        # kept open deliberately - CTkImage converts it lazily, not at construction time
        brand_icon = ctk.CTkImage(
            light_image=Image_module.open(resource_path("icons/pickaxe.ico")), size=(30, 30)
        )
        ctk.CTkLabel(brand, text="", image=brand_icon).grid(column=0, row=0)
        ctk.CTkLabel(
            brand,
            text="Drops Miner",
            font=ctk.CTkFont(size=15, weight="bold"),
            text_color=PALETTE["fg"],
        ).grid(column=1, row=0, padx=(10, 0))

        # Notebook (manual tab-switching content area, below the top bar)
        self.tabs = Notebook(self, root_frame)

        nav_values = [
            _("gui", "tabs", "main"),
            _("gui", "tabs", "inventory"),
            _("gui", "tabs", "settings"),
            _("gui", "tabs", "help"),
        ]
        # Custom nav pills instead of CTkSegmentedButton: the mockup's active tab is a
        # white pill with violet text on a tinted track, but CTkSegmentedButton only
        # supports one text_color for every segment (selected and not), so it can't
        # tell them apart the way the mockup does - plain CTkButtons can.
        nav_track = ctk.CTkFrame(topbar, corner_radius=10, fg_color=PALETTE["bg"])
        nav_track.grid(column=1, row=0)
        self._nav_buttons: dict[str, ctk.CTkButton] = {}

        def select_nav(name: str) -> None:
            self.tabs.select(name)
            for btn_name, btn in self._nav_buttons.items():
                active = btn_name == name
                btn.configure(
                    fg_color=PALETTE["surface"] if active else "transparent",
                    text_color=PALETTE["accent"] if active else PALETTE["muted"],
                )

        for i, name in enumerate(nav_values):
            btn = ctk.CTkButton(
                nav_track,
                text=name,
                corner_radius=8,
                fg_color="transparent",
                hover_color=PALETTE["border"],
                text_color=PALETTE["muted"],
                font=ctk.CTkFont(weight="bold"),
                command=partial(select_nav, name),
            )
            btn.grid(column=i, row=0, padx=3, pady=3)
            self._nav_buttons[name] = btn
        # mark the first tab active without re-selecting it (Notebook already starts there)
        self._nav_buttons[nav_values[0]].configure(
            fg_color=PALETTE["surface"], text_color=PALETTE["accent"]
        )

        # Tray icon - minimize button, far right of the top bar
        self.tray = TrayIcon(self, topbar)

        # Main tab: a flexible left column (hero + channels) and a FIXED-width
        # right sidebar (account/login, connection, activity log), matching the
        # Clarity mockup's fixed ~360px sidebar rather than a proportional split
        # (which turned out to depend unpredictably on each side's natural
        # content size instead of the weight ratio).
        main_frame = self.tabs.add_tab(name=nav_values[0])
        main_frame.columnconfigure(0, weight=1)
        main_frame.columnconfigure(1, weight=0)
        main_frame.rowconfigure(0, weight=1)
        main_left = ctk.CTkFrame(main_frame, fg_color="transparent")
        main_left.grid(column=0, row=0, sticky="nsew", padx=(0, 10))
        main_left.columnconfigure(0, weight=1)
        main_left.rowconfigure(1, weight=1)
        main_right = ctk.CTkFrame(main_frame, fg_color="transparent", width=360)
        main_right.grid(column=1, row=0, sticky="ns")
        main_right.grid_propagate(False)
        main_right.columnconfigure(0, weight=1)
        main_right.rowconfigure(2, weight=1)

        self.progress = CampaignProgress(self, main_left)
        self.status = StatusBar(self, self.progress.badge_slot)
        self.channels = ChannelList(self, main_left)
        self.login = LoginForm(self, main_right)
        self.websockets = WebsocketStatus(self, main_right)
        self.output = ConsoleOutput(self, main_right)
        # Inventory tab
        inv_frame = self.tabs.add_tab(name=_("gui", "tabs", "inventory"))
        self.inv = InventoryOverview(self, inv_frame)
        # Settings tab
        settings_frame = self.tabs.add_tab(name=_("gui", "tabs", "settings"))
        self.settings = SettingsPanel(self, settings_frame)
        # Help tab
        help_frame = self.tabs.add_tab(name=_("gui", "tabs", "help"))
        self.help = HelpTab(self, help_frame)
        # clamp minimum window size (update geometry first), and open at the same
        # size as the Clarity mockup's canvas instead of whatever width the sum of
        # natural widget sizes happens to add up to
        root.update_idletasks()
        root.minsize(width=1000, height=700)
        # Windows can restore a maximized state for this window from a previous run
        # regardless of geometry() below - force it back to a normal, un-maximized
        # window first so the 1440x900 size below actually takes effect.
        root.state("normal")
        root.geometry("1440x900")
        # register logging handler
        self._handler = _TKOutputHandler(self)
        self._handler.setFormatter(OUTPUT_FORMATTER)
        logger = logging.getLogger("TwitchDrops")
        logger.addHandler(self._handler)
        if (logging_level := logger.getEffectiveLevel()) < logging.ERROR:
            self.print(f"Logging level: {logging.getLevelName(logging_level)}")
        # gracefully handle Windows shutdown closing the application
        if sys.platform == "win32":
            # NOTE: this root.update() is required for the below to work - don't remove
            root.update()
            self._message_map = {
                # window close request
                win32con.WM_CLOSE: self.close,
                # shutdown request
                win32con.WM_QUERYENDSESSION: self.close,
            }
            # This hooks up the wnd_proc function as the message processor for the root window.
            self.old_wnd_proc = win32gui.SetWindowLong(
                self._handle, win32con.GWL_WNDPROC, self.wnd_proc
            )
            # This ensures all of this works when the application is withdrawn or iconified
            ctypes.windll.user32.ShutdownBlockReasonCreate(
                self._handle, ctypes.c_wchar_p(_("gui", "status", "exiting"))
            )
            # DEV NOTE: use this to remove the reason in the future
            # ctypes.windll.user32.ShutdownBlockReasonDestroy(self._handle)
        else:
            # use old-style window closing protocol for non-windows platforms
            root.protocol("WM_DELETE_WINDOW", self.close)
            root.protocol("WM_DESTROY_WINDOW", self.close)
        # Apply the full palette now that all widgets have been created
        self.apply_theme(self._twitch.settings.dark_mode)
        # stay hidden in tray if needed, otherwise show the window when everything's ready
        if self._twitch.settings.tray and sys.platform != "darwin":
            # NOTE: this starts the tray icon thread
            self._root.after_idle(self.tray.minimize)
        else:
            self._root.after_idle(self._root.deiconify)

    def wnd_proc(self, hwnd, msg, w_param, l_param):
        """
        This function serves as a message processor for all messages sent
        to the application by Windows.
        """
        if msg == win32con.WM_DESTROY:
            win32api.SetWindowLong(self._handle, win32con.GWL_WNDPROC, self.old_wnd_proc)
        if msg in self._message_map:
            return self._message_map[msg](w_param, l_param)
        return win32gui.CallWindowProc(self.old_wnd_proc, hwnd, msg, w_param, l_param)

    @cached_property
    def _handle(self) -> int:
        return int(self._root.wm_frame(), 16)

    @property
    def running(self) -> bool:
        return self._poll_task is not None

    @property
    def close_requested(self) -> bool:
        return self._close_requested.is_set()

    async def wait_until_closed(self):
        # wait until the user closes the window
        await self._close_requested.wait()

    async def coro_unless_closed(self, coro: abc.Awaitable[_T]) -> _T:
        # In Python 3.11, we need to explicitly wrap awaitables
        tasks = [asyncio.ensure_future(coro), asyncio.ensure_future(self._close_requested.wait())]
        done: set[asyncio.Task[Any]]
        pending: set[asyncio.Task[Any]]
        done, pending = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
        for task in pending:
            task.cancel()
        if self._close_requested.is_set():
            raise ExitRequest()
        return await next(iter(done))

    def prevent_close(self):
        self._close_requested.clear()

    def start(self):
        if self._poll_task is None:
            self._poll_task = asyncio.create_task(self._poll())
        # self.progress.start_timer()

    def stop(self):
        self.progress.stop_timer()
        if self._poll_task is not None:
            self._poll_task.cancel()
            self._poll_task = None

    async def _poll(self):
        """
        This runs the Tkinter event loop via asyncio instead of calling mainloop.
        0.05s gives similar performance and CPU usage.
        Not ideal, but the simplest way to avoid threads, thread safety,
        loop.call_soon_threadsafe, futures and all of that.

        Uses TKINTER_DONT_WAIT to prevent Tcl/Tk from hanging inside native
        system calls (e.g. X11/Wayland input contexts) during heavy UI redraws.
        """
        do_one_event = self._root.dooneevent
        # TKINTER_DONT_WAIT (1 << 1) tells Tcl to return immediately
        # if no events are ready in the queue.
        DONT_WAIT = 1 << 1

        while True:
            try:
                # Drain pending Tk events non-blockingly
                while do_one_event(DONT_WAIT):
                    pass
            except tk.TclError:
                # Root window was destroyed
                break
            await asyncio.sleep(0.05)

        self._poll_task = None

    def close(self, *args) -> int:
        """
        Requests the GUI application to close.
        The window itself will be closed in the closing sequence later.
        """
        self._close_requested.set()
        # notify client we're supposed to close
        self._twitch.close()
        return 0

    def close_window(self):
        """
        Closes the window. Invalidates the logger.
        """
        self.tray.stop()
        logging.getLogger("TwitchDrops").removeHandler(self._handler)
        self._root.destroy()

    def unfocus(self, event):
        # support pressing ESC to unfocus
        self._root.focus_set()
        self.channels.clear_selection()
        self.settings.clear_selection()

    # these are here to interface with underlaying GUI components
    def save(self, *, force: bool = False) -> None:
        self._cache.save(force=force)

    def grab_attention(self, *, sound: bool = True):
        self.tray.restore()
        self._root.focus_set()
        if sound:
            self._root.bell()

    def set_games(self, games: set[Game]) -> None:
        self.settings.set_games(games)

    def display_drop(
        self, drop: TimedDrop, *, countdown: bool = True, subone: bool = False
    ) -> None:
        self.progress.display(drop, countdown=countdown, subone=subone)  # main tab
        # inventory overview is updated from within drops themselves via change events
        self.tray.update_title(drop)  # tray

    def clear_drop(self):
        self.progress.display(None)
        self.tray.update_title(None)

    def print(self, message: str):
        # print to our custom output
        self.output.print(message)

    def _set_title_bar_color(self, color: int) -> None:
        """
        Set the Windows title bar color to match the theme.
        Only works on Windows with DWM enabled.

        Args:
            color: ARGB color value (e.g., 0x001E1E1E for dark gray).
        """
        if sys.platform != "win32":
            return
        # DWMWA_CAPTION_COLOR = 35
        DWMWA_CAPTION_COLOR = 35
        hwnd = self._root.winfo_id()
        frame_hwnd = ctypes.windll.user32.GetParent(hwnd)
        color_value = ctypes.c_int(color)
        ctypes.windll.dwmapi.DwmSetWindowAttribute(
            frame_hwnd,
            DWMWA_CAPTION_COLOR,
            ctypes.byref(color_value),
            ctypes.sizeof(ctypes.c_int),
        )

    def apply_theme(self, dark: bool) -> None:
        """
        Switch CustomTkinter's global appearance mode (every CTk widget built with
        a (light, dark) PALETTE tuple re-colors itself automatically), then manually
        re-theme the handful of things that aren't CTk and so aren't appearance-mode
        aware: ttk's Treeview + its Scrollbar (CustomTkinter has no table/treeview
        widget), the priority/exclude tk.Listbox-es (same reason), and OS-level chrome.
        """
        ctk.set_appearance_mode("dark" if dark else "light")

        # Setting theme for macOS
        if sys.platform == "darwin":
            app = AppKit.NSApplication.sharedApplication()
            if dark:
                appearance = AppKit.NSAppearance.appearanceNamed_(AppKit.NSAppearanceNameDarkAqua)
            else:
                appearance = AppKit.NSAppearance.appearanceNamed_(AppKit.NSAppearanceNameAqua)
            app.setAppearance_(appearance)

        mode = 1 if dark else 0
        bg = PALETTE["bg"][mode]
        fg = PALETTE["fg"][mode]
        surface = PALETTE["surface"][mode]
        border = PALETTE["border"][mode]
        muted = PALETTE["muted"][mode]
        sel_bg = PALETTE["sel"][mode]
        sel_fg = fg
        ok = PALETTE["ok"][mode]
        warn = PALETTE["warn"][mode]

        # A handful of plain ttk.Frame/Label widgets remain (e.g. image-bearing labels,
        # where CTkLabel would need a CTkImage instead of the cache's plain PhotoImage)
        s = self._style
        s.configure("TFrame", background=surface)
        s.configure("TLabel", background=surface, foreground=fg)

        # Priority/Exclude listboxes (plain tk.Listbox, no CTk equivalent)
        self.settings._priority_list.configure_theme(
            bg=surface, fg=fg, sel_bg=sel_bg, sel_fg=sel_fg
        )
        self.settings._exclude_list.configure_theme(
            bg=surface, fg=fg, sel_bg=sel_bg, sel_fg=sel_fg
        )
        # Channel list status / watching row colors (ttk Treeview tags)
        self.channels.configure_theme(
            watching_bg=sel_bg, online_fg=ok, pending_fg=warn, offline_fg=muted
        )

        # Set Windows title bar color to match the theme
        if dark:
            # Use dark gray color 0x001E1E1E (ARGB format, matches bg color #1e1e1e)
            self._set_title_bar_color(0x001E1E1E)
        else:
            # Reset to system default title bar color
            self._set_title_bar_color(0xFFFFFFFF)

        # the hero card icon's rounded corners are baked into the image using the
        # current surface color (see CampaignProgress._render_icon) - force it to
        # re-render so they match the new theme instead of staying the old color
        self.progress._icon_rendered_size = (0, 0)
        self.progress._render_icon()


###################
# GUI MANAGER END #
###################


if __name__ == "__main__":
    # Everything below is for debug purposes only
    import aiohttp
    from types import SimpleNamespace

    class StrNamespace(SimpleNamespace):
        __hash__ = object.__hash__  # type: ignore

        def __str__(self):
            if hasattr(self, "_str__"):
                return self._str__(self)
            return super().__str__()

    class HashNamespace(SimpleNamespace):
        __hash__ = object.__hash__  # type: ignore

    def create_game(id: int, name: str):
        return StrNamespace(name=name, id=id, _str__=lambda s: s.name)

    iid = 0

    def create_channel(
        name: str,
        status: int,
        game: str | None,
        drops: bool,
        viewers: int,
        acl_based: bool,
    ):
        # status: 0 -> OFFLINE, 1 -> PENDING_ONLINE, 2 -> ONLINE
        if status == 1:
            status = False
            pending = True
        else:
            pending = False
        if game is not None:
            game_obj: StrNamespace | None = create_game(0, game)
        else:
            game_obj = None
        global iid
        return SimpleNamespace(
            name=name,
            iid=(iid := iid + 1),
            online=bool(status),
            pending_online=pending,
            game=game_obj,
            drops_enabled=drops,
            viewers=viewers,
            acl_based=acl_based,
        )

    def create_drop(
        campaign_name: str,
        game_name: str,
        rewards: list[str],
        claimed_drops: int,
        total_drops: int,
        current_minutes: int,
        total_minutes: int,
    ):
        cd = claimed_drops
        td = total_drops
        cm = current_minutes
        tm = total_minutes
        ref_stamp = datetime.now(timezone.utc)
        drop_image_url = (
            "https://static-cdn.jtvnw.net/twitch-quests-assets/"
            "REWARD/e0ede26e-b071-47f0-af5f-b80b26fa9fb4.png"
        )
        campaign_image_url = "https://static-cdn.jtvnw.net/ttv-boxart/515025-120x160.jpg"
        benefits = [SimpleNamespace(name=name, image_url=drop_image_url) for name in rewards]
        mock = SimpleNamespace(
            id="0",
            campaign=HashNamespace(
                name=campaign_name,
                id="campaign",
                game=create_game(0, game_name),
                expired=False,
                active=False,
                upcoming=True,
                eligible=False,
                finished=False,
                link_url="https://google.com",
                image_url=campaign_image_url,
                allowed_channels=[],
                starts_at=ref_stamp,
                ends_at=ref_stamp + timedelta(days=7),
                timed_drops={},
                claimed_drops=cd,
                total_drops=td,
                required_minutes=tm,
                remaining_drops=td - cd,
                progress=(cd * tm + cm) / (td * tm),
                remaining_minutes=(td - cd) * tm - cm,
            ),
            image_url=drop_image_url,
            can_claim=False,
            can_earn=lambda: False,
            is_claimed=False,
            preconditions=True,
            benefits=benefits,
            rewards_text=lambda: ', '.join(b.name for b in benefits),
            starts_at=ref_stamp + timedelta(seconds=2),
            ends_at=ref_stamp + timedelta(days=7) - timedelta(seconds=2),
            progress=cm/tm,
            current_minutes=cm,
            required_minutes=tm,
            remaining_minutes=tm-cm,
        )
        mock.campaign.timed_drops["0"] = mock
        mock.campaign.drops = mock.campaign.timed_drops.values()
        return mock

    async def main(exit_event: asyncio.Event):
        # Initialize GUI debug
        mock = SimpleNamespace(
            settings=SimpleNamespace(
                tray=False,
                priority=[],
                proxy=URL(),
                dark_mode=False,
                alter=lambda: None,
                language="English",
                autostart_tray=False,
                exclude={"Lit Game"},
                tray_notifications=True,
                enable_badges_emotes=False,
                available_drops_check=False,
                logging_level=LOGGING_LEVELS[0],
                priority_mode=PriorityMode.PRIORITY_ONLY,
            )
        )
        mock.change_state = lambda state: mock.gui.print(f"State change: {state.value}")
        mock.state_change = lambda state: partial(mock.change_state, state)
        mock.request = aiohttp.request
        # _.set_language("Русский")
        gui = GUIManager(mock)  # type: ignore
        mock.gui = gui
        mock.close = gui.stop
        gui.start()
        assert gui._poll_task is not None
        gui._poll_task.add_done_callback(lambda t: exit_event.set())
        # Login form
        gui.login.update("Login required", None)
        # Game selector and settings panel games
        gui.set_games(set([
            create_game(420690, "Lit Game"),
            create_game(123456, "Best Game"),
            create_game(654321, "My Game Very Long Name"),
        ]))
        # Channel list
        gui.channels.display(
            create_channel(
                name="Thomus",
                status=0,
                game=None,
                drops=False,
                viewers=0,
                acl_based=True,
            ),
            add=True,
        )
        channel = create_channel(
            name="Traitus", status=1, game=None, drops=False, viewers=0, acl_based=True
        )
        gui.channels.display(channel, add=True)
        gui.channels.set_watching(channel)
        gui.channels.display(
            create_channel(
                name="Testus",
                status=2,
                game="Best Game",
                drops=True,
                viewers=42,
                acl_based=False,
            ),
            add=True,
        )
        gui.channels.display(
            create_channel(
                name="Livus",
                status=2,
                game="Best Game",
                drops=True,
                viewers=69,
                acl_based=False,
            ),
            add=True,
        )
        gui._root.update()
        gui.channels.get_selection()
        # Inventory overview
        drop = create_drop(
            "Wardrobe Cleaning", "Cleaning Masters", ["Fancy Pants"], 2, 7, 0, 240
        )
        campaign = drop.campaign
        await gui.inv.add_campaign(campaign)

        gui.print("Single-line test message")
        await asyncio.sleep(1)
        gui.print("Multi-line\ntest\nmessage")

        # Tray
        # gui.tray.minimize()
        await asyncio.sleep(2)
        claim_text = (
            f"{campaign.game.name}\n"
            f"{drop.rewards_text()} ({campaign.claimed_drops}/{campaign.total_drops})"
        )
        gui.tray.notify(claim_text, "Mined Drop")

        # Drop progress
        gui.display_drop(drop, countdown=False)
        await asyncio.sleep(3)

        gui.progress.start_timer()
        await asyncio.sleep(5)

        gui.clear_drop()
        await asyncio.sleep(5)

        campaign.can_earn = lambda: True
        gui.inv.update_drop(drop)
        gui.display_drop(drop)
        await asyncio.sleep(10)

        drop.current_minutes = 239
        drop.remaining_minutes = 1
        drop.progress = 239/240
        campaign.remaining_minutes -= 1
        gui.inv.update_drop(drop)
        gui.display_drop(drop)
        await asyncio.sleep(63)

        drop.current_minutes = 240
        drop.remaining_minutes = 0
        drop.progress = 1.0
        campaign.remaining_minutes -= 1
        campaign.progress = 3/7
        campaign.claimed_drops = 3
        campaign.remaining_drops = 4
        gui.inv.update_drop(drop)
        gui.display_drop(drop)

    def main_exit(task: asyncio.Task[None]) -> None:
        if task.exception() is not None:
            exit_event.set()

    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    exit_event = asyncio.Event()
    main_task = loop.create_task(main(exit_event))
    main_task.add_done_callback(main_exit)
    loop.run_until_complete(exit_event.wait())
    if main_task.done():
        loop.run_until_complete(main_task)
