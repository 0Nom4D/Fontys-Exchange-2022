import 'dart:io';
import 'dart:typed_data';

import 'package:flutter/cupertino.dart';

enum ImageSource {
  gallery,
  camera
}

class ImageViewer extends StatelessWidget {
  const ImageViewer({required this.imageSource, this.imagePath, this.imageData, super.key});

  final ImageSource imageSource;
  final Uint8List? imageData;
  final String? imagePath;

  @override
  Widget build(BuildContext context) {
    return imageSource == ImageSource.gallery && imageData != null
      ? Image.memory(
        imageData!,
        fit: BoxFit.contain,
        width: MediaQuery.of(context).size.width,
        height: MediaQuery.of(context).size.height * .80,
        filterQuality: FilterQuality.high,
      ) : Image.file(
        File(imagePath!),
        fit: BoxFit.contain,
        width: MediaQuery.of(context).size.width,
        height: MediaQuery.of(context).size.height * .80,
        filterQuality: FilterQuality.high,
      );
  }
}