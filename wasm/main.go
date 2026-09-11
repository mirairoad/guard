//go:build js && wasm

// The browser renderer imports the same generated routes and templ components
// as the server. Guard's client routes are data-free shells; their Mount hooks
// start the typed JSON work after the new markup is painted.
package main

import (
	"context"
	"html"
	"strings"
	"syscall/js"

	"github.com/hushkey-app/guard/client/pages"
	"github.com/mirairoad/howl-go/core/dom"
	"github.com/mirairoad/howl-go/core/router"
	"github.com/mirairoad/howl-go/core/state"
)

var routes = pages.FsClientRoutes()

func mount(_ js.Value, args []js.Value) any {
	if len(args) < 2 {
		return nil
	}
	route, _, ok := router.Lookup(routes, canonical(args[0].String()))
	if ok && route.Mount != nil {
		dom.Mount(args[1], route.Mount) // opens the scope its effects and listeners are released with
	}
	return nil
}

func unmount(_ js.Value, args []js.Value) any {
	if len(args) < 1 {
		return nil
	}
	route, _, ok := router.Lookup(routes, canonical(args[0].String()))
	if ok {
		dom.Unmount(route.Unmount) // nil is fine: the scope Mount opened is disposed either way
	}
	return nil
}

func render(_ js.Value, args []js.Value) any {
	if len(args) < 2 {
		return ""
	}
	path := canonical(args[0].String())
	route, params, ok := router.Lookup(routes, path)
	if !ok || !route.Client {
		return ""
	}

	ctx := router.WithRoutes(context.Background(), routes)
	ctx = router.WithCurrent(ctx, path)
	ctx = router.WithParams(ctx, params)
	payload, err := router.DecodeRenderPayload(args[1].String())
	if err != nil {
		return ""
	}
	ctx, err = state.Hydrate[pages.Bootstrap](ctx, payload.Bootstrap)
	if err != nil {
		return ""
	}

	var output strings.Builder
	title, head := route.HeadParts(ctx, route.Label)
	output.WriteString("<template data-head><title>" + html.EscapeString(title) + "</title>" + head + "</template>")
	if err := route.Component().Render(ctx, &output); err != nil {
		return ""
	}
	return output.String()
}

func canonical(path string) string {
	if len(path) > 1 {
		return strings.TrimSuffix(path, "/")
	}
	return path
}

func main() {
	js.Global().Set("howlRender", js.FuncOf(render))
	js.Global().Set("howlMount", js.FuncOf(mount))
	js.Global().Set("howlUnmount", js.FuncOf(unmount))

	out := make([]any, 0, len(routes))
	for _, route := range routes {
		out = append(out, map[string]any{"path": route.Pattern, "label": route.Label, "client": route.Client})
	}
	js.Global().Set("howlRoutes", js.ValueOf(out))
	select {}
}
