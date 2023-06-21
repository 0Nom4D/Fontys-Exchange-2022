import 'package:flutter/material.dart';
import 'dart:io';

import 'package:psv_fan_experience/src/widgets/parallelogram.dart';

class PictureOverlay extends StatelessWidget {
  const PictureOverlay({
    super.key,
    required this.imageAsset,
    required this.username,
    required this.userAvatar,
    required this.competitionName,
    required this.isFromAssets
  });

  final String imageAsset;
  final String username;
  final String userAvatar;
  final String competitionName;
  final bool isFromAssets;

  @override
  Widget build(BuildContext context) {
    return SizedBox(
      width: MediaQuery.of(context).size.width,
      height: MediaQuery.of(context).size.height * .45,
      child: Card(
        semanticContainer: true,
        clipBehavior: Clip.antiAliasWithSaveLayer,
        shape: const RoundedRectangleBorder(
          borderRadius: BorderRadius.only(
            topLeft: Radius.circular(20),
            topRight: Radius.circular(20),
            bottomLeft: Radius.circular(30),
            bottomRight: Radius.circular(30)
          )
        ),
        child: Stack(
          alignment: AlignmentDirectional.center,
          children: [
            isFromAssets ? Image.asset(
              imageAsset,
              fit: BoxFit.cover,
              width: MediaQuery.of(context).size.width,
            ) : Image.file(
              File(imageAsset),
              fit: BoxFit.cover,
              width: MediaQuery.of(context).size.width,
            ),
            Positioned.fill(
              child: Align(
                alignment: Alignment.topLeft,
                child: Padding(
                  padding: EdgeInsets.only(
                    top: MediaQuery.of(context).size.height * .015,
                    left: MediaQuery.of(context).size.width * .03
                  ),
                  child: Stack(
                    children: [
                      Positioned(
                        top: 3,
                        left: 27,
                        child: ClipPath(
                          clipper: Parallelogram(),
                          child: DecoratedBox(
                            decoration: BoxDecoration(
                              color: Theme.of(context).colorScheme.secondary
                            ),
                            child: Padding(
                              padding: const EdgeInsets.only(left: 20, right: 25, top: 5, bottom: 5),
                              child: Text(
                                username,
                                textAlign: TextAlign.right,
                                style: TextStyle(
                                  color: Theme.of(context).colorScheme.tertiary,
                                  fontSize: 18
                                ),
                              ),
                            ),
                          ),
                        ),
                      ),
                      Positioned(
                        top: 0,
                        child: CircleAvatar(
                          child: Image.asset(userAvatar),
                        ),
                      ),
                    ],
                  ),
                ),
              ),
            ),
            Positioned.fill(
              child: Align(
                alignment: Alignment.bottomRight,
                child: DecoratedBox(
                  decoration: BoxDecoration(
                    borderRadius: const BorderRadius.only(
                      topLeft: Radius.circular(10),
                      bottomLeft: Radius.circular(0)
                    ),
                    color: Theme.of(context).colorScheme.secondary
                  ),
                  child: Padding(
                    padding: EdgeInsets.all(MediaQuery.of(context).size.width * .019),
                    child: Text(
                      competitionName,
                      textAlign: TextAlign.center,
                      style: TextStyle(
                        color: Theme.of(context).colorScheme.tertiary,
                        fontSize: 18
                      ),
                    ),
                  ),
                ),
              )
            ),
          ]
        ),
      ),
    );
  }
}
