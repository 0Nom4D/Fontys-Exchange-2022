import 'package:flutter/material.dart';

import 'package:app/src/models/achievements.dart';

class BadgeImage extends StatelessWidget {
  const BadgeImage({
    required this.name,
    required this.asset,
    this.description = "",
    required this.isLong,
    required this.isLocked,
    super.key
  });

  BadgeImage.from(Achievement model, this.isLong, {super.key})
      : asset = model.imageAsset,
        name = model.title,
        description = model.description,
        isLocked = model.isLocked;

  final String name;
  final String description;
  final String asset;
  final bool isLong;
  final bool isLocked;

  @override
  Widget build(BuildContext context) {
    return isLong ? SizedBox(
      width: MediaQuery.of(context).size.width,
      height: MediaQuery.of(context).size.height * .075,
      child: Row(
        mainAxisAlignment: MainAxisAlignment.center,
        children: [
          Badge(asset: asset, isLocked: isLocked),
          const SizedBox(width: 10),
          SizedBox(
            width: MediaQuery.of(context).size.width * .6,
            child: Column(
              mainAxisAlignment: MainAxisAlignment.center,
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                Text(
                  name,
                  textAlign: TextAlign.left,
                  style: const TextStyle(
                    color: Colors.white,
                    fontSize: 20,
                    fontWeight: FontWeight.bold
                  ),
                ),
                Text(
                  description,
                  textAlign: TextAlign.left,
                  style: const TextStyle(
                    color: Colors.grey,
                    fontSize: 10
                  ),
                ),
              ],
            ),
          )
        ]
      ),
    ) : SizedBox(
      width: MediaQuery.of(context).size.height * .2,
      height: MediaQuery.of(context).size.height * .2,
      child: Column(
        children: [
          Stack(
            alignment: AlignmentDirectional.center,
            children: [
              Container(
                width: MediaQuery.of(context).size.height * .09,
                height: MediaQuery.of(context).size.height * .09,
                decoration: BoxDecoration(
                  borderRadius: BorderRadius.circular(12),
                  gradient: LinearGradient(
                    colors: [
                      Colors.white,
                      Colors.white.withOpacity(.2)
                    ],
                    begin: Alignment.topCenter,
                    end: Alignment.bottomCenter
                  )
                ),
              ),
              Badge(asset: asset, isLocked: isLocked)
            ],
          ),
          const SizedBox(height: 5),
          SizedBox(
            width: MediaQuery.of(context).size.height * .09,
            child: Text(
              name,
              textAlign: TextAlign.center,
              style: const TextStyle(
                color: Colors.white,
                fontSize: 15,
                fontWeight: FontWeight.bold
              ),
            ),
          ),
        ]
      )
    );
  }
}

class Badge extends StatelessWidget {
  const Badge({
    required this.asset,
    required this.isLocked,
    super.key
  });

  final String asset;
  final bool isLocked;

  @override
  Widget build(BuildContext context) {
    return Stack(
      alignment: Alignment.center,
      children: [
        Image.asset("assets/$asset.png", fit: BoxFit.cover),
        if (isLocked)
          const Icon(Icons.lock, color: Colors.white),
      ],
    );
  }
}
