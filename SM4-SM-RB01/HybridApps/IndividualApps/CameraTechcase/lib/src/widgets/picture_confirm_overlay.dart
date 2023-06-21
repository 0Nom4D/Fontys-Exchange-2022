import 'dart:io';
import 'package:camera_techcase/src/widgets/aligned_action_button.dart';
import 'package:flutter/material.dart';

import 'package:gallery_saver_plus/gallery_saver.dart';
import 'package:go_router/go_router.dart';
import 'package:camera/camera.dart';

import 'package:camera_techcase/src/widgets/image_viewer.dart';
import 'package:camera_techcase/src/theme.dart';

class PictureConfirmOverlay extends StatefulWidget {
  const PictureConfirmOverlay({required this.uploadPicture, super.key});

  final XFile uploadPicture;

  @override
  State<PictureConfirmOverlay> createState() => _PictureConfirmOverlayState();
}

class _PictureConfirmOverlayState extends State<PictureConfirmOverlay> {
  @override
  Widget build(BuildContext context) {
    return Stack(
      alignment: Alignment.center,
      children: [
        ImageViewer(imagePath: widget.uploadPicture.path, imageSource: ImageSource.gallery),
        Image.file(
          File(widget.uploadPicture.path),
          fit: BoxFit.contain,
          width: MediaQuery.of(context).size.width,
          height: MediaQuery.of(context).size.height * .80
        ),
        AlignedActionButton(
          label: 'CANCEL',
          backgroundColor: Theme.of(context).colorScheme.tertiary,
          alignment: Alignment.bottomLeft,
          callback: () async {
            Future.delayed(const Duration(seconds: 2), () {
              GoRouter.of(context).canPop() ? GoRouter.of(context).pop() : null;
            });
          }
        ),
        AlignedActionButton(
          label: 'SAVE',
          backgroundColor: successColor,
          alignment: Alignment.bottomRight,
          callback: () async {
            bool? success = await GallerySaver.saveImage(widget.uploadPicture.path);

            if (!mounted) {
              return;
            }

            if (success!) {
              ScaffoldMessenger.of(context).showSnackBar(
                const SnackBar(
                  content: Text(
                    "You photo has been saved to your gallery!"
                  )
                )
              );

              Future.delayed(const Duration(seconds: 2), () {
                context.go('/camera');
              });
            } else {
              ScaffoldMessenger.of(context).showSnackBar(
                const SnackBar(
                  content: Text(
                    "An unexpected error occurred when saving your picture to your gallery."
                  )
                )
              );
            }
          }
        )
      ],
    );
  }
}