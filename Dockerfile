FROM node:22

WORKDIR /app

COPY . .

RUN npm install 

ENV NODE_ENV=production

CMD ["node", "index.js"]
