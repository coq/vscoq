import { defineConfig } from "vite";
import { resolve } from "path";
import dts from 'vite-plugin-dts';
import react from "@vitejs/plugin-react";
import { externalizeDeps } from 'vite-plugin-externalize-deps';
import { libInjectCss} from 'vite-plugin-lib-inject-css';

// https://vitejs.dev/config/
export default defineConfig( ({mode}) => ({
  plugins: [
    react(),
    dts(),
    externalizeDeps(),
    libInjectCss()
  ],
  sourcemap: "inline",
  build: {
    lib: {
        entry: resolve(__dirname, 'src/main.tsx'),
        formats: ['es']
    }
  },
}));
